open Ir
open Ast
open Reg_alloc

let align16 n = (n + 15) / 16 * 16

let spill_temp1 = "t5"
let spill_temp2 = "t6"

let resolve_src reg_map spill_base temp = function
  | VImm 0 -> ("zero", "")
  | VImm n -> (temp, Printf.sprintf "  li %s, %d\n" temp n)
  | VReg 0 -> ("sp", "")
  | VReg r ->
    match Hashtbl.find_opt reg_map r with
    | Some (Reg reg) -> (reg, "")
    | Some (Spill off) ->
      (temp, Printf.sprintf "  lw %s, %d(sp)\n" temp (spill_base + off))
    | None -> (temp, Printf.sprintf "  li %s, 0  # unalloc vreg %d\n" temp r)

let resolve_dst reg_map spill_base temp rd =
  match Hashtbl.find_opt reg_map rd with
  | Some (Reg reg) -> (reg, "")
  | Some (Spill off) ->
    (temp, Printf.sprintf "  sw %s, %d(sp)\n" temp (spill_base + off))
  | None -> failwith ("vreg " ^ string_of_int rd ^ " not allocated")

let resolve_base reg_map spill_base base =
  match Hashtbl.find_opt reg_map base with
  | Some (Reg reg) -> (reg, "")
  | Some (Spill off) ->
    (spill_temp2, Printf.sprintf "  lw %s, %d(sp)\n" spill_temp2 (spill_base + off))
  | None -> failwith ("vreg " ^ string_of_int base ^ " not allocated")

let riscv_binop = function
  | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div" | Mod -> "rem"
  | _ -> "??"

let fits_imm12 n =
  n >= -2048 && n <= 2047

let is_positive_power_of_two n =
  n > 0 && n land (n - 1) = 0

let log2_power_of_two n =
  let rec loop shift value =
    if value = 1 then shift else loop (shift + 1) (value lsr 1)
  in
  loop 0 n

let signed_power_of_two_magnitude n =
  let magnitude = if n < 0 then -n else n in
  if magnitude > 1 && is_positive_power_of_two magnitude then
    Some magnitude
  else None

type multiply_shape =
  | ShiftOnly of int
  | ShiftAdd of int
  | ShiftSub of int

let cheap_multiply_shape n =
  let n = normalize_i32 n in
  let magnitude = if n < 0 then -n else n in
  if magnitude <= 1 then None
  else if is_positive_power_of_two magnitude then
    Some (ShiftOnly (log2_power_of_two magnitude), n < 0)
  else if is_positive_power_of_two (magnitude - 1) then
    Some (ShiftAdd (log2_power_of_two (magnitude - 1)), n < 0)
  else if is_positive_power_of_two (magnitude + 1) then
    Some (ShiftSub (log2_power_of_two (magnitude + 1)), n < 0)
  else None

(* Compute the multiplier and post-shift for exact signed division by a
   non-power-of-two constant.  This is the 32-bit form of the algorithm used
   by LLVM's SignedDivisionByConstantInfo (Hacker's Delight, chapter 10). *)
let signed_division_magic divisor =
  let divisor = normalize_i32 divisor in
  let d = Int64.of_int divisor in
  let ad = Int64.abs d in
  let two31 = Int64.shift_left 1L 31 in
  let t = Int64.add two31 (if divisor < 0 then 1L else 0L) in
  let anc = Int64.sub (Int64.sub t 1L) (Int64.rem t ad) in
  let p = ref 31 in
  let q1 = ref (Int64.div two31 anc) in
  let r1 = ref (Int64.sub two31 (Int64.mul !q1 anc)) in
  let q2 = ref (Int64.div two31 ad) in
  let r2 = ref (Int64.sub two31 (Int64.mul !q2 ad)) in
  let delta = ref 0L in
  let continue = ref true in
  while !continue do
    incr p;
    q1 := Int64.mul !q1 2L;
    r1 := Int64.mul !r1 2L;
    if Int64.compare !r1 anc >= 0 then begin
      q1 := Int64.add !q1 1L;
      r1 := Int64.sub !r1 anc
    end;
    q2 := Int64.mul !q2 2L;
    r2 := Int64.mul !r2 2L;
    if Int64.compare !r2 ad >= 0 then begin
      q2 := Int64.add !q2 1L;
      r2 := Int64.sub !r2 ad
    end;
    delta := Int64.sub ad !r2;
    continue :=
      Int64.compare !q1 !delta < 0 ||
      (Int64.compare !q1 !delta = 0 && !r1 = 0L)
  done;
  let magic = Int64.add !q2 1L in
  let magic = if divisor < 0 then Int64.neg magic else magic in
  let low32 = Int64.logand magic 0xffff_ffffL in
  let signed_magic =
    if Int64.compare low32 two31 >= 0 then
      Int64.sub low32 0x1_0000_0000L
    else low32
  in
  (Int64.to_int signed_magic, !p - 32)

let is_compare = function
  | Eq | Neq | Lt | Gt | Le | Ge -> true
  | Add | Sub | Mul | Div | Mod | And | Or -> false

let emit_compare_branch buf spill_base reg_map branch_if_true op v1 v2 label =
  let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
  let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
  let mnemonic, lhs, rhs =
    match op, branch_if_true with
    | Eq, true  | Neq, false -> ("beq", r1, r2)
    | Eq, false | Neq, true  -> ("bne", r1, r2)
    | Lt, true  | Ge, false  -> ("blt", r1, r2)
    | Lt, false | Ge, true   -> ("bge", r1, r2)
    | Gt, true  | Le, false  -> ("blt", r2, r1)
    | Gt, false | Le, true   -> ("bge", r2, r1)
    | _ -> assert false
  in
  Buffer.add_string buf l1;
  Buffer.add_string buf l2;
  Buffer.add_string buf
    (Printf.sprintf "  %s %s, %s, %s\n" mnemonic lhs rhs label)

let emit_cheap_multiply buf spill_base reg_map rd value constant =
  let shape, negate = Option.get (cheap_multiply_shape constant) in
  let (src, load) = resolve_src reg_map spill_base spill_temp1 value in
  let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
  Buffer.add_string buf load;
  (match shape with
   | ShiftOnly shift ->
     Buffer.add_string buf
       (Printf.sprintf "  slli %s, %s, %d\n" dst src shift)
   | ShiftAdd shift ->
     Buffer.add_string buf
       (Printf.sprintf "  slli %s, %s, %d\n  add %s, %s, %s\n"
          spill_temp2 src shift dst spill_temp2 src)
   | ShiftSub shift ->
     Buffer.add_string buf
       (Printf.sprintf "  slli %s, %s, %d\n  sub %s, %s, %s\n"
          spill_temp2 src shift dst spill_temp2 src));
  if negate then
    Buffer.add_string buf (Printf.sprintf "  neg %s, %s\n" dst dst);
  Buffer.add_string buf store

let emit_one buf spill_base reg_map = function
  | Binop (rd, Add, v, VImm n) when fits_imm12 n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  addi %s, %s, %d\n" dst src n);
    Buffer.add_string buf store
  | Binop (rd, Add, VImm n, v) when fits_imm12 n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  addi %s, %s, %d\n" dst src n);
    Buffer.add_string buf store
  | Binop (rd, Sub, v, VImm n)
    when n <> min_int && fits_imm12 (-n) ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  addi %s, %s, %d\n" dst src (-n));
    Buffer.add_string buf store
  | Binop (rd, ((Div | Mod) as op), v, VImm divisor)
    when signed_power_of_two_magnitude divisor <> None ->
    let magnitude = Option.get (signed_power_of_two_magnitude divisor) in
    let shift = log2_power_of_two magnitude in
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    (* Signed division rounds toward zero, so negative dividends receive a
       2^k-1 bias before the arithmetic shift.  The same bias gives C's
       signed remainder after masking. *)
    Buffer.add_string buf
      (Printf.sprintf "  srai %s, %s, 31\n  srli %s, %s, %d\n"
         spill_temp2 src spill_temp2 spill_temp2 (32 - shift));
    Buffer.add_string buf
      (Printf.sprintf "  add %s, %s, %s\n" dst src spill_temp2);
    (match op with
     | Div ->
       Buffer.add_string buf
         (Printf.sprintf "  srai %s, %s, %d\n" dst dst shift);
       if divisor < 0 then
         Buffer.add_string buf (Printf.sprintf "  neg %s, %s\n" dst dst)
     | Mod ->
       let mask = magnitude - 1 in
       if fits_imm12 mask then
         Buffer.add_string buf
           (Printf.sprintf "  andi %s, %s, %d\n" dst dst mask)
       else
         Buffer.add_string buf
           (Printf.sprintf "  slli %s, %s, %d\n  srli %s, %s, %d\n"
              dst dst (32 - shift) dst dst (32 - shift));
       Buffer.add_string buf
         (Printf.sprintf "  sub %s, %s, %s\n" dst dst spill_temp2)
     | _ -> assert false);
    Buffer.add_string buf store
  | Binop (rd, ((Div | Mod) as op), v, VImm raw_divisor)
    when
      let divisor = normalize_i32 raw_divisor in
      divisor <> 0 && divisor <> 1 && divisor <> -1 &&
      signed_power_of_two_magnitude divisor = None ->
    let divisor = normalize_i32 raw_divisor in
    let magic, shift = signed_division_magic divisor in
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    let original, reload_original =
      if op = Mod && src = dst then
        if load = "" then begin
          Buffer.add_string buf
            (Printf.sprintf "  mv %s, %s\n" spill_temp1 src);
          (spill_temp1, "")
        end else
          (src, load)
      else
        (src, "")
    in
    (* [mulh x, y, x] is legal: both inputs are consumed before x is
       overwritten, so t6 can hold the magic constant and then the quotient. *)
    Buffer.add_string buf
      (Printf.sprintf "  li %s, %d\n  mulh %s, %s, %s\n"
         spill_temp2 magic spill_temp2 src spill_temp2);
    if divisor > 0 && magic < 0 then
      Buffer.add_string buf
        (Printf.sprintf "  add %s, %s, %s\n"
           spill_temp2 spill_temp2 src)
    else if divisor < 0 && magic > 0 then
      Buffer.add_string buf
        (Printf.sprintf "  sub %s, %s, %s\n"
           spill_temp2 spill_temp2 src);
    if shift > 0 then
      Buffer.add_string buf
        (Printf.sprintf "  srai %s, %s, %d\n"
           spill_temp2 spill_temp2 shift);
    Buffer.add_string buf
      (Printf.sprintf "  srli %s, %s, 31\n  add %s, %s, %s\n"
         dst spill_temp2 spill_temp2 spill_temp2 dst);
    (match op with
     | Div ->
       if dst <> spill_temp2 then
         Buffer.add_string buf
           (Printf.sprintf "  mv %s, %s\n" dst spill_temp2)
     | Mod ->
       Buffer.add_string buf
         (Printf.sprintf "  li %s, %d\n  mul %s, %s, %s\n"
            dst divisor spill_temp2 spill_temp2 dst);
       Buffer.add_string buf reload_original;
       Buffer.add_string buf
         (Printf.sprintf "  sub %s, %s, %s\n" dst original spill_temp2)
     | _ -> assert false);
    Buffer.add_string buf store
  | Binop (rd, Mul, value, VImm constant)
    when cheap_multiply_shape constant <> None ->
    emit_cheap_multiply buf spill_base reg_map rd value constant
  | Binop (rd, Mul, VImm constant, value)
    when cheap_multiply_shape constant <> None ->
    emit_cheap_multiply buf spill_base reg_map rd value constant
  | Binop (rd, Mul, v, VImm n) when is_positive_power_of_two n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  slli %s, %s, %d\n"
         dst src (log2_power_of_two n));
    Buffer.add_string buf store
  | Binop (rd, Mul, VImm n, v) when is_positive_power_of_two n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  slli %s, %s, %d\n"
         dst src (log2_power_of_two n));
    Buffer.add_string buf store
  | Binop (rd, Eq, v, VImm 0)
  | Binop (rd, Eq, VImm 0, v) ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf (Printf.sprintf "  seqz %s, %s\n" dst src);
    Buffer.add_string buf store
  | Binop (rd, Neq, v, VImm 0)
  | Binop (rd, Neq, VImm 0, v) ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf (Printf.sprintf "  snez %s, %s\n" dst src);
    Buffer.add_string buf store
  | Binop (rd, Lt, v, VImm n)
  | Binop (rd, Gt, VImm n, v)
    when fits_imm12 n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  slti %s, %s, %d\n" dst src n);
    Buffer.add_string buf store
  | Binop (rd, Ge, v, VImm n)
  | Binop (rd, Le, VImm n, v)
    when fits_imm12 n ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  slti %s, %s, %d\n  xori %s, %s, 1\n"
         dst src n dst dst);
    Buffer.add_string buf store
  | Binop (rd, ((Le | Gt) as op), v, VImm n)
    when n < max_int && fits_imm12 (n + 1) ->
    let (src, load) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, store) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf load;
    Buffer.add_string buf
      (Printf.sprintf "  slti %s, %s, %d\n" dst src (n + 1));
    if op = Gt then
      Buffer.add_string buf
        (Printf.sprintf "  xori %s, %s, 1\n" dst dst);
    Buffer.add_string buf store
  | Binop (rd, Eq, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  sub %s, %s, %s\n  seqz %s, %s\n"
                             dst r1 r2 dst dst);
    Buffer.add_string buf st
  | Binop (rd, Neq, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  sub %s, %s, %s\n  snez %s, %s\n"
                             dst r1 r2 dst dst);
    Buffer.add_string buf st
  | Binop (rd, Lt, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  slt %s, %s, %s\n" dst r1 r2);
    Buffer.add_string buf st
  | Binop (rd, Gt, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  slt %s, %s, %s\n" dst r2 r1);
    Buffer.add_string buf st
  | Binop (rd, Le, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n"
                             dst r2 r1 dst dst);
    Buffer.add_string buf st
  | Binop (rd, Ge, v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n"
                             dst r1 r2 dst dst);
    Buffer.add_string buf st
  | Binop (rd, (Add | Sub | Mul | Div | Mod as op), v1, v2) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v1 in
    let (r2, l2) = resolve_src reg_map spill_base spill_temp2 v2 in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf l2;
    Buffer.add_string buf (Printf.sprintf "  %s %s, %s, %s\n" (riscv_binop op) dst r1 r2);
    Buffer.add_string buf st
  | Binop _ -> ()
  | Unop (rd, Neg, v) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf (Printf.sprintf "  neg %s, %s\n" dst r1);
    Buffer.add_string buf st
  | Unop (rd, Not, v) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    Buffer.add_string buf (Printf.sprintf "  seqz %s, %s\n" dst r1);
    Buffer.add_string buf st
  | Unop (rd, Pos, v) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    if dst <> r1 then
      Buffer.add_string buf (Printf.sprintf "  mv %s, %s\n" dst r1);
    Buffer.add_string buf st
  | Li (rd, n) ->
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf (Printf.sprintf "  li %s, %d\n" dst n);
    Buffer.add_string buf st
  | Mov (rd, v) ->
    let (r1, l1) = resolve_src reg_map spill_base spill_temp1 v in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf l1;
    if dst <> r1 then
      Buffer.add_string buf (Printf.sprintf "  mv %s, %s\n" dst r1);
    Buffer.add_string buf st
  | Lw (rd, 0, off) ->
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" dst off);
    Buffer.add_string buf st
  | Lw (rd, base, off) ->
    let (rbase, lbase) = resolve_base reg_map spill_base base in
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf lbase;
    Buffer.add_string buf (Printf.sprintf "  lw %s, %d(%s)\n" dst off rbase);
    Buffer.add_string buf st
  | Sw (0, off, v) ->
    let (rv, lv) = resolve_src reg_map spill_base spill_temp1 v in
    Buffer.add_string buf lv;
    Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" rv off)
  | Sw (base, off, v) ->
    let (rbase, lbase) = resolve_base reg_map spill_base base in
    let (rv, lv) = resolve_src reg_map spill_base spill_temp1 v in
    Buffer.add_string buf lbase;
    Buffer.add_string buf lv;
    Buffer.add_string buf (Printf.sprintf "  sw %s, %d(%s)\n" rv off rbase)
  | La (rd, name) ->
    let (dst, st) = resolve_dst reg_map spill_base spill_temp1 rd in
    Buffer.add_string buf (Printf.sprintf "  la %s, %s\n" dst name);
    Buffer.add_string buf st
  | Call (rd, fname, args) ->
    let n_args = List.length args in
    let excess = if n_args > 8 then n_args - 8 else 0 in
    let adj = if excess = 0 then 0 else align16 (excess * 4) in
    let call_spill_base = spill_base + adj in
    if adj > 0 then
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (-adj));
    if excess > 0 then begin
      let rec copy_excess i arg_list =
        match arg_list with
        | [] -> ()
        | v :: rst when i >= 8 ->
          let (rv, lv) = resolve_src reg_map call_spill_base spill_temp1 v in
          Buffer.add_string buf lv;
          Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" rv ((i - 8) * 4));
          copy_excess (i + 1) rst
        | _ :: rst -> copy_excess (i + 1) rst
      in
      copy_excess 0 args
    end;
    List.iteri (fun i v ->
      if i < 8 then begin
        let areg = "a" ^ string_of_int i in
        let (rv, lv) = resolve_src reg_map call_spill_base areg v in
        Buffer.add_string buf lv;
        if rv <> areg then
          Buffer.add_string buf (Printf.sprintf "  mv %s, %s\n" areg rv)
      end
    ) args;
    Buffer.add_string buf (Printf.sprintf "  jal ra, %s\n" fname);
    let (dst, st) = resolve_dst reg_map call_spill_base spill_temp1 rd in
    if dst <> "a0" then
      Buffer.add_string buf (Printf.sprintf "  mv %s, a0\n" dst);
    Buffer.add_string buf st;
    if adj > 0 then
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" adj)
  | Ret _ -> ()
  | Jmp label ->
    Buffer.add_string buf (Printf.sprintf "  j %s\n" label)
  | Bz (v, label) ->
    let (rv, lv) = resolve_src reg_map spill_base spill_temp1 v in
    Buffer.add_string buf lv;
    Buffer.add_string buf (Printf.sprintf "  beqz %s, %s\n" rv label)
  | Bnz (v, label) ->
    let (rv, lv) = resolve_src reg_map spill_base spill_temp1 v in
    Buffer.add_string buf lv;
    Buffer.add_string buf (Printf.sprintf "  bnez %s, %s\n" rv label)
  | Label name ->
    Buffer.add_string buf (Printf.sprintf "%s:\n" name)

let effective_stack_size body =
  List.fold_left (fun size -> function
    | Lw (_, 0, off) | Sw (0, off, _) -> max size (off + 4)
    | _ -> size
  ) 0 body

let emit_func buf (f : func_ir) (fa : func_alloc) =
  (* IR generation reserves a slot for every source local.  After promotion,
     forwarding and inlining, many of those slots no longer occur in the IR.
     Recompute the actually-addressed prefix so dead locals do not force a
     frame in otherwise register-only leaf functions. *)
  let stack_sz = effective_stack_size f.fir_body in
  let spill_sz = fa.fa_spill_sz in
  (* main terminates via ecall and never returns to an ABI caller, so saving
     its s-register colors only adds entry/exit memory traffic. *)
  let saved_callee =
    if f.fir_name = "main" then [] else fa.fa_callee_used
  in
  let callee_count = List.length saved_callee in
  let has_call =
    List.exists (function Ir.Call _ -> true | _ -> false) f.fir_body
  in
  let save_ra = f.fir_name <> "main" && has_call in
  let ra_off = stack_sz + spill_sz + callee_count * 4 in
  let frame_bytes = ra_off + (if save_ra then 4 else 0) in
  let total_frame = align16 frame_bytes in
  let spill_base = stack_sz in

  let ret_label = "." ^ f.fir_name ^ "_ret" in

  if f.fir_name = "main" then
    Buffer.add_string buf (Printf.sprintf "\n  .globl %s\n" f.fir_name);
  Buffer.add_string buf (Printf.sprintf "%s:\n" f.fir_name);
  if total_frame > 0 then
    Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (-total_frame));
  if save_ra then
    Buffer.add_string buf (Printf.sprintf "  sw ra, %d(sp)\n" ra_off);

  List.iteri (fun i reg ->
    let off = stack_sz + spill_sz + i * 4 in
    Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" reg off)
  ) saved_callee;

  let n_params = List.length f.fir_params in
  for i = 0 to n_params - 1 do
    let vreg = i + 1 in
    if i < 8 then begin
      let areg = "a" ^ string_of_int i in
      match Hashtbl.find_opt fa.fa_reg_map vreg with
      | Some (Reg r) ->
        if r <> areg then
          Buffer.add_string buf (Printf.sprintf "  mv %s, %s\n" r areg)
      | Some (Spill off) ->
        Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" areg (spill_base + off))
      | None -> ()
    end else begin
      let caller_off = total_frame + (i - 8) * 4 in
      match Hashtbl.find_opt fa.fa_reg_map vreg with
      | Some (Reg r) ->
        Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" r caller_off)
      | Some (Spill off) ->
        Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" spill_temp1 caller_off);
        Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" spill_temp1 (spill_base + off))
      | None -> ()
    end
  done;

  let use_counts = Hashtbl.create 64 in
  let note_value = function
    | VImm _ | VReg 0 -> ()
    | VReg r ->
      let old =
        match Hashtbl.find_opt use_counts r with Some n -> n | None -> 0
      in
      Hashtbl.replace use_counts r (old + 1)
  in
  List.iter (function
    | Binop (_, _, v1, v2) -> note_value v1; note_value v2
    | Unop (_, _, v) | Mov (_, v) -> note_value v
    | Lw (_, base, _) -> note_value (VReg base)
    | Sw (base, _, v) -> note_value (VReg base); note_value v
    | Call (_, _, args) -> List.iter note_value args
    | Ret (Some v) | Bz (v, _) | Bnz (v, _) -> note_value v
    | Li _ | La _ | Ret None | Jmp _ | Label _ -> ()
  ) f.fir_body;
  let used_once r =
    Hashtbl.find_opt use_counts r = Some 1
  in
  let rec emit_body = function
    | Binop (rd, op, v1, v2) :: Bz (VReg branch_r, label) :: rest
      when rd = branch_r && used_once rd && is_compare op ->
      emit_compare_branch buf spill_base fa.fa_reg_map false op v1 v2 label;
      emit_body rest
    | Binop (rd, op, v1, v2) :: Bnz (VReg branch_r, label) :: rest
      when rd = branch_r && used_once rd && is_compare op ->
      emit_compare_branch buf spill_base fa.fa_reg_map true op v1 v2 label;
      emit_body rest
    | Unop (rd, Not, v) :: Bz (VReg branch_r, label) :: rest
      when rd = branch_r && used_once rd ->
      emit_one buf spill_base fa.fa_reg_map (Bnz (v, label));
      emit_body rest
    | Unop (rd, Not, v) :: Bnz (VReg branch_r, label) :: rest
      when rd = branch_r && used_once rd ->
      emit_one buf spill_base fa.fa_reg_map (Bz (v, label));
      emit_body rest
    | Ret (Some v) :: [] ->
      let (rv, lv) = resolve_src fa.fa_reg_map spill_base "a0" v in
      Buffer.add_string buf lv;
      if rv <> "a0" then
        Buffer.add_string buf (Printf.sprintf "  mv a0, %s\n" rv)
    | Ret None :: [] ->
      ()
    | Ret (Some v) :: rest ->
      let (rv, lv) = resolve_src fa.fa_reg_map spill_base "a0" v in
      Buffer.add_string buf lv;
      if rv <> "a0" then
        Buffer.add_string buf (Printf.sprintf "  mv a0, %s\n" rv);
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label);
      emit_body rest
    | Ret None :: rest ->
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label);
      emit_body rest
    | instr :: rest ->
      emit_one buf spill_base fa.fa_reg_map instr;
      emit_body rest
    | [] -> ()
  in
  emit_body f.fir_body;

  Buffer.add_string buf (Printf.sprintf "%s:\n" ret_label);
  if f.fir_name = "main" then begin
    List.iteri (fun i reg ->
      let off = stack_sz + spill_sz + i * 4 in
      Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" reg off)
    ) saved_callee;
    if total_frame > 0 then
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" total_frame);
    Buffer.add_string buf "  li a7, 93\n";
    Buffer.add_string buf "  ecall\n"
  end else begin
    List.iteri (fun i reg ->
      let off = stack_sz + spill_sz + i * 4 in
      Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" reg off)
    ) saved_callee;
    if save_ra then
      Buffer.add_string buf (Printf.sprintf "  lw ra, %d(sp)\n" ra_off);
    if total_frame > 0 then
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" total_frame);
    Buffer.add_string buf "  ret\n"
  end

let emit_globals buf globals =
  if globals <> [] then begin
    Buffer.add_string buf ".data\n";
    List.iter (fun (name, init) ->
      Buffer.add_string buf (Printf.sprintf "  .globl %s\n" name);
      Buffer.add_string buf (Printf.sprintf "%s: .word %d\n" name init)
    ) globals;
    Buffer.add_string buf "\n"
  end

let gen (m : module_ir) =
  let buf = Buffer.create 65536 in
  emit_globals buf m.mir_globals;
  Buffer.add_string buf ".text\n";
  List.iter (fun f ->
    let fa = Reg_alloc.alloc_func f in
    emit_func buf f fa
  ) m.mir_functions;
  print_string (Buffer.contents buf)
