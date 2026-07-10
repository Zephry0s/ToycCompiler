open Ir
open Ast
open Reg_alloc

let align16 n = (n + 15) / 16 * 16

let spill_temp1 = "t5"
let spill_temp2 = "t6"

let resolve_src reg_map spill_base temp = function
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

let emit_one buf spill_base reg_map = function
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
    let call_spill_base = spill_base + excess * 4 in
    if excess > 0 then begin
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (-(excess * 4)));
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
    Buffer.add_string buf (Printf.sprintf "  mv %s, a0\n" dst);
    Buffer.add_string buf st;
    if excess > 0 then
      Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (excess * 4))
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

let emit_func buf f (fa : func_alloc) =
  let stack_sz = f.fir_stack_sz in
  let spill_sz = fa.fa_spill_sz in
  let callee_count = List.length fa.fa_callee_used in
  let total_frame = align16 (stack_sz + spill_sz + callee_count * 4 + 4) in
  let ra_off = total_frame - 4 in
  let spill_base = stack_sz in

  let ret_label = "." ^ f.fir_name ^ "_ret" in

  if f.fir_name = "main" then
    Buffer.add_string buf (Printf.sprintf "\n  .globl %s\n" f.fir_name);
  Buffer.add_string buf (Printf.sprintf "%s:\n" f.fir_name);
  Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (-total_frame));
  Buffer.add_string buf (Printf.sprintf "  sw ra, %d(sp)\n" ra_off);

  List.iteri (fun i reg ->
    let off = stack_sz + spill_sz + i * 4 in
    Buffer.add_string buf (Printf.sprintf "  sw %s, %d(sp)\n" reg off)
  ) fa.fa_callee_used;

  let n_params = List.length f.fir_params in
  for i = 0 to n_params - 1 do
    let vreg = i + 1 in
    if i < 8 then begin
      let areg = "a" ^ string_of_int i in
      match Hashtbl.find_opt fa.fa_reg_map vreg with
      | Some (Reg r) ->
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

  List.iter (function
    | Ret (Some v) ->
      let (rv, lv) = resolve_src fa.fa_reg_map spill_base "a0" v in
      Buffer.add_string buf lv;
      if rv <> "a0" then
        Buffer.add_string buf (Printf.sprintf "  mv a0, %s\n" rv);
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label)
    | Ret None ->
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label)
    | instr ->
      emit_one buf spill_base fa.fa_reg_map instr
  ) f.fir_body;

  Buffer.add_string buf (Printf.sprintf "%s:\n" ret_label);
  if f.fir_name = "main" then begin
    List.iteri (fun i reg ->
      let off = stack_sz + spill_sz + i * 4 in
      Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" reg off)
    ) fa.fa_callee_used;
    Buffer.add_string buf (Printf.sprintf "  lw ra, %d(sp)\n" ra_off);
    Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" total_frame);
    Buffer.add_string buf "  li a7, 93\n";
    Buffer.add_string buf "  ecall\n"
  end else begin
    List.iteri (fun i reg ->
      let off = stack_sz + spill_sz + i * 4 in
      Buffer.add_string buf (Printf.sprintf "  lw %s, %d(sp)\n" reg off)
    ) fa.fa_callee_used;
    Buffer.add_string buf (Printf.sprintf "  lw ra, %d(sp)\n" ra_off);
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
