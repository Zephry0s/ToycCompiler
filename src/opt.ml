open Ast
open Ir

let max_iterations = 5

(* --- Utility --- *)

let eval_binop op a b = match op with
  | Add -> a + b | Sub -> a - b | Mul -> a * b
  | Div -> a / b | Mod -> a mod b
  | And -> if a <> 0 && b <> 0 then 1 else 0
  | Or  -> if a <> 0 || b <> 0 then 1 else 0
  | Eq  -> if a = b  then 1 else 0
  | Neq -> if a <> b then 1 else 0
  | Lt  -> if a < b  then 1 else 0
  | Gt  -> if a > b  then 1 else 0
  | Le  -> if a <= b then 1 else 0
  | Ge  -> if a >= b then 1 else 0

let eval_uop op n = match op with
  | Neg -> -n | Pos -> n | Not -> if n = 0 then 1 else 0

let has_side_effect = function
  | Sw _ | Call _ | Ret _ | Jmp _ | Bz _ | Bnz _ | Label _ -> true
  | _ -> false

let def_vreg = function
  | Binop (rd, _, _, _) | Unop (rd, _, _) | Li (rd, _) | Mov (rd, _)
  | Lw (rd, _, _) | La (rd, _) | Call (rd, _, _) -> Some rd
  | _ -> None

let vreg_of_val = function VReg r -> [r] | VImm _ -> []

let src_vregs = function
  | Binop (_, _, v1, v2) -> vreg_of_val v1 @ vreg_of_val v2
  | Unop (_, _, v) | Mov (_, v) -> vreg_of_val v
  | Lw (_, base, _) -> [base]
  | Sw (base, _, v) -> base :: vreg_of_val v
  | Call (_, _, args) ->
    List.fold_left (fun acc v -> acc @ vreg_of_val v) [] args
  | Ret (Some v) -> vreg_of_val v
  | Ret None -> []
  | Bz (v, _) | Bnz (v, _) -> vreg_of_val v
  | Li _ | La _ | Jmp _ | Label _ -> []

(* --- Basic block partitioning for copy propagation --- *)

let split_blocks (instrs : instr list) : instr list list =
  let arr = Array.of_list instrs in
  let n = Array.length arr in
  if n = 0 then [] else begin
    let starts = Array.make n false in
    starts.(0) <- true;
    for i = 0 to n - 1 do
      match arr.(i) with
      | Label _ -> starts.(i) <- true
      | Jmp _ | Bz _ | Bnz _ | Ret _ ->
        if i + 1 < n then starts.(i + 1) <- true
      | _ -> ()
    done;
    let blocks = ref [] in
    let i = ref 0 in
    while !i < n do
      if starts.(!i) then begin
        let start = !i in
        let j = ref (start + 1) in
        while !j < n && not starts.(!j) do incr j done;
        let blk = Array.to_list (Array.sub arr start (!j - start)) in
        blocks := blk :: !blocks;
        i := !j
      end else
        incr i
    done;
    List.rev !blocks
  end

(* --- Value substitution for copy propagation --- *)

let rec subst_val (subst : (vreg, value) Hashtbl.t) (v : value) : value =
  subst_val_depth 0 subst v

and subst_val_depth (depth : int) (subst : (vreg, value) Hashtbl.t) (v : value) : value =
  if depth > 5 then v else
  match v with
  | VImm _ -> v
  | VReg r when r = 0 -> v
  | VReg r ->
    match Hashtbl.find_opt subst r with
    | Some v' -> subst_val_depth (depth + 1) subst v'
    | None -> v

let subst_base (subst : (vreg, value) Hashtbl.t) (base : vreg) : vreg =
  match Hashtbl.find_opt subst base with
  | Some (VReg r) -> r
  | _ -> base

let subst_instr (subst : (vreg, value) Hashtbl.t) (i : instr) : instr =
  let sv = subst_val subst in
  let sb = subst_base subst in
  match i with
  | Binop (rd, op, v1, v2) -> Binop (rd, op, sv v1, sv v2)
  | Unop (rd, op, v) -> Unop (rd, op, sv v)
  | Mov (rd, v) -> Mov (rd, sv v)
  | Lw (rd, base, off) -> Lw (rd, sb base, off)
  | Sw (base, off, v) -> Sw (sb base, off, sv v)
  | Call (rd, name, args) -> Call (rd, name, List.map sv args)
  | Ret (Some v) -> Ret (Some (sv v))
  | Ret None -> Ret None
  | Bz (v, lbl) -> Bz (sv v, lbl)
  | Bnz (v, lbl) -> Bnz (sv v, lbl)
  | Li _ | La _ | Jmp _ | Label _ -> i

(* --- Pass 1: Constant Folding --- *)

let const_fold (instrs : instr list) : instr list =
  List.map (fun i -> match i with
    | Binop (rd, op, VImm a, VImm b) ->
      (match op with
       | Div | Mod when b = 0 -> i
       | _ -> Li (rd, eval_binop op a b))
    | Unop (rd, op, VImm n) ->
      Li (rd, eval_uop op n)
    | Mov (rd, VImm n) ->
      Li (rd, n)
    | _ -> i
  ) instrs

(* --- Pass 2: Algebraic Simplification --- *)

let alg_simplify (instrs : instr list) : instr list =
  List.map (fun i -> match i with
    | Binop (rd, Add, v, VImm 0) | Binop (rd, Add, VImm 0, v) -> Mov (rd, v)
    | Binop (rd, Sub, v, VImm 0) -> Mov (rd, v)
    | Binop (rd, Mul, v, VImm 1) | Binop (rd, Mul, VImm 1, v) -> Mov (rd, v)
    | Binop (rd, Mul, _, VImm 0) | Binop (rd, Mul, VImm 0, _) -> Li (rd, 0)
    | Binop (rd, Div, v, VImm 1) -> Mov (rd, v)
    | Binop (rd, Div, VImm 0, VImm n) when n <> 0 -> Li (rd, 0)
    | Binop (rd, Mod, _, VImm 1) -> Li (rd, 0)
    | Binop (rd, Mod, VImm 0, VImm n) when n <> 0 -> Li (rd, 0)
    | Binop (rd, Sub, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 0)
    | Binop (rd, Eq, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 1)
    | Binop (rd, Neq, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 0)
    | _ -> i
  ) instrs

(* --- Pass 2.5: Strength Reduction --- *)

let strength_reduce (instrs : instr list) : instr list =
  List.map (fun i -> match i with
    | Binop (rd, Mul, v, VImm 2) | Binop (rd, Mul, VImm 2, v) ->
      Binop (rd, Add, v, v)
    | _ -> i
  ) instrs

(* --- Pass 3: Copy Propagation --- *)

let copy_prop_block (instrs : instr list) : instr list =
  let subst = Hashtbl.create 16 in
  let changed = ref false in
  let result = List.map (fun i ->
    let i' = subst_instr subst i in
    if i' <> i then changed := true;
    (match def_vreg i' with
     | Some rd ->
       Hashtbl.remove subst rd;
       (match i' with
        | Mov (_, v) when not (has_side_effect i') -> Hashtbl.replace subst rd v
        | Li (_, n) when not (has_side_effect i') -> Hashtbl.replace subst rd (VImm n)
        | _ -> ())
     | None -> ());
    i'
  ) instrs in
  if !changed then result else instrs

let copy_prop (instrs : instr list) : instr list =
  let blocks = split_blocks instrs in
  let blocks' = List.map copy_prop_block blocks in
  List.fold_left (@) [] blocks'

(* --- Pass 4: Dead Code Elimination --- *)

let dead_code_elim (instrs : instr list) : instr list =
  let instr_arr = Array.of_list instrs in
  let n = Array.length instr_arr in
  let def_map = Hashtbl.create 64 in
  let side_effect_idxs = ref [] in
  for idx = 0 to n - 1 do
    (match def_vreg instr_arr.(idx) with
     | Some rd ->
       let existing = match Hashtbl.find_opt def_map rd with
         | Some idxs -> idxs | None -> []
       in
       Hashtbl.replace def_map rd (idx :: existing)
     | None -> ());
    if has_side_effect instr_arr.(idx) then
      side_effect_idxs := idx :: !side_effect_idxs
  done;
  let live = Array.make n false in
  let worklist = Queue.create () in
  let enqueue r = if r <> 0 then Queue.add r worklist in
  List.iter (fun idx ->
    live.(idx) <- true;
    List.iter enqueue (src_vregs instr_arr.(idx))
  ) !side_effect_idxs;
  while not (Queue.is_empty worklist) do
    let r = Queue.take worklist in
    if r <> 0 then
      match Hashtbl.find_opt def_map r with
      | Some idxs ->
        List.iter (fun idx ->
          if not live.(idx) then begin
            live.(idx) <- true;
            List.iter enqueue (src_vregs instr_arr.(idx))
          end
        ) idxs
      | None -> ()
  done;
  let result = ref [] in
  for idx = 0 to n - 1 do
    if live.(idx) then result := instr_arr.(idx) :: !result
  done;
  List.rev !result

(* --- Pass 5: Peephole --- *)

let rec peephole_scan (acc : instr list) (instrs : instr list) : instr list =
  match instrs with
  | [] -> List.rev acc
  | (Li _ as li) :: (Bz (VReg r, lbl)) :: rest ->
    (match li with
     | Li (rd, 0) when rd = r -> peephole_scan (li :: acc) (Jmp lbl :: rest)
     | Li (rd, n) when rd = r && n <> 0 -> peephole_scan (li :: acc) rest
     | _ -> peephole_scan (Bz (VReg r, lbl) :: li :: acc) rest)
  | (Li _ as li) :: (Bnz (VReg r, lbl)) :: rest ->
    (match li with
     | Li (rd, n) when rd = r && n <> 0 -> peephole_scan (li :: acc) (Jmp lbl :: rest)
     | Li (rd, 0) when rd = r -> peephole_scan (li :: acc) rest
     | _ -> peephole_scan (Bnz (VReg r, lbl) :: li :: acc) rest)
  | Bz (VImm 0, lbl) :: rest -> peephole_scan acc (Jmp lbl :: rest)
  | Bz (VImm _, _) :: rest -> peephole_scan acc rest
  | Bnz (VImm 0, _) :: rest -> peephole_scan acc rest
  | Bnz (VImm n, lbl) :: rest when n <> 0 -> peephole_scan acc (Jmp lbl :: rest)
  | (Jmp lbl1) :: (Label lbl2) :: rest when lbl1 = lbl2 ->
    peephole_scan (Label lbl2 :: acc) rest
  | i :: rest -> peephole_scan (i :: acc) rest

let peephole (instrs : instr list) : instr list =
  peephole_scan [] instrs

(* --- Pass 6: Dead code after unconditional jumps --- *)

let remove_dead_after_jmp (instrs : instr list) : instr list =
  let arr = Array.of_list instrs in
  let n = Array.length arr in
  let keep = Array.make n true in
  for i = 0 to n - 1 do
    match arr.(i) with
    | Jmp _ | Ret _ ->
      let j = ref (i + 1) in
      while !j < n do
        match arr.(!j) with
        | Label _ -> j := n
        | _ -> keep.(!j) <- false; incr j
      done
    | _ -> ()
  done;
  let result = ref [] in
  for i = 0 to n - 1 do
    if keep.(i) then result := arr.(i) :: !result
  done;
  List.rev !result

(* ================================================================
 * Loop Unrolling
 * ================================================================ *)

module SMap = Map.Make(String)
module ISet = Set.Make(struct type t = int let compare = compare end)
module IMap = Map.Make(struct type t = int let compare = compare end)

type bbinfo = {
  b_start : int;
  b_end   : int;
  b_label : string option;
  mutable b_succs : int list;
}

let build_cfg (instrs : instr list) : (instr array * bbinfo array) =
  let arr = Array.of_list instrs in
  let n = Array.length arr in
  let starts = Array.make n false in
  if n > 0 then starts.(0) <- true;
  for i = 0 to n - 1 do
    match arr.(i) with
    | Label _ -> starts.(i) <- true
    | Jmp _ | Bz _ | Bnz _ | Ret _ ->
      if i + 1 < n then starts.(i + 1) <- true
    | _ -> ()
  done;
  let blocks = ref [] in
  let label_map = ref SMap.empty in
  let block_id = ref 0 in
  let i = ref 0 in
  while !i < n do
    if starts.(!i) then begin
      let start = !i in
      let label = match arr.(start) with Label s -> Some s | _ -> None in
      (match label with Some s -> label_map := SMap.add s !block_id !label_map | None -> ());
      let j = ref (start + 1) in
      while !j < n && not starts.(!j) do incr j done;
      blocks := { b_start = start; b_end = !j - 1; b_label = label; b_succs = [] } :: !blocks;
      incr block_id;
      i := !j
    end else incr i
  done;
  let bbs = Array.of_list (List.rev !blocks) in
  for bid = 0 to Array.length bbs - 1 do
    let last = arr.(bbs.(bid).b_end) in
    bbs.(bid).b_succs <- (match last with
      | Jmp lbl -> (match SMap.find_opt lbl !label_map with Some id -> [id] | None -> [])
      | Ret _ -> []
      | Bz (_, lbl) | Bnz (_, lbl) ->
        let tgt = match SMap.find_opt lbl !label_map with Some id -> [id] | None -> [] in
        let fall = if bid + 1 < Array.length bbs then [bid + 1] else [] in
        tgt @ fall
      | _ -> if bid + 1 < Array.length bbs then [bid + 1] else [])
  done;
  (arr, bbs)

let find_max_vreg (body : instr list) : int =
  let max_r = ref 0 in
  let check = function VReg r -> if r > !max_r then max_r := r | _ -> () in
  List.iter (function
    | Binop (rd, _, v1, v2) -> max_r := max !max_r rd; check v1; check v2
    | Unop (rd, _, v) | Mov (rd, v) -> max_r := max !max_r rd; check v
    | Li (rd, _) | Lw (rd, _, _) | La (rd, _) | Call (rd, _, _) ->
        max_r := max !max_r rd
    | Sw (_, _, v) -> check v
    | Ret (Some v) -> check v
    | Bz (v, _) | Bnz (v, _) -> check v
    | _ -> ()
  ) body;
  !max_r

(* rename vregs in an instruction: old -> new mapping *)
let rename_instr (rmap : int IMap.t) (i : instr) : instr =
  let rv = function VReg r -> VReg (try IMap.find r rmap with Not_found -> r)
                   | v -> v in
  let rd r = try IMap.find r rmap with Not_found -> r in
  match i with
  | Binop (r, op, v1, v2) -> Binop (rd r, op, rv v1, rv v2)
  | Unop (r, op, v) -> Unop (rd r, op, rv v)
  | Mov (r, v) -> Mov (rd r, rv v)
  | Li (r, n) -> Li (rd r, n)
  | Lw (r, b, off) -> Lw (rd r, b, off)
  | La (r, name) -> La (rd r, name)
  | Call (r, name, args) -> Call (rd r, name, List.map rv args)
  | Sw (b, off, v) -> Sw (b, off, rv v)
  | Ret (Some v) -> Ret (Some (rv v))
  | Ret None -> i
  | Bz (v, lbl) -> Bz (rv v, lbl)
  | Bnz (v, lbl) -> Bnz (rv v, lbl)
  | Label _ | Jmp _ -> i

(* collect vregs defined in an instruction list *)
let collect_defs (instrs : instr list) : ISet.t =
  let s = ref ISet.empty in
  List.iter (fun i ->
    match def_vreg i with Some r -> s := ISet.add r !s | None -> ()
  ) instrs;
  !s

let unroll_func (f : func_ir) : func_ir =
  let arr, bbs = build_cfg f.fir_body in
  let nbb = Array.length bbs in
  let loops = ref [] in
  for bid = 0 to nbb - 1 do
    List.iter (fun succ ->
      if succ <= bid then loops := (bid, succ) :: !loops
    ) bbs.(bid).b_succs
  done;
  if !loops = [] then f
  else begin
    let max_vreg = find_max_vreg f.fir_body in
    let next_vreg = ref (max_vreg + 1) in
    let insert = Array.make (Array.length arr) [] in
    let remove = Array.make (Array.length arr) false in

    List.iter (fun (tail, header) ->
      let hstart = bbs.(header).b_start in
      let hend = bbs.(header).b_end in
      let tstart = bbs.(tail).b_start in
      let tend = bbs.(tail).b_end in

      let body_instrs = ref [] in
      for j = hstart to hend do body_instrs := arr.(j) :: !body_instrs done;
      for j = tstart to tend do body_instrs := arr.(j) :: !body_instrs done;
      let body_instrs = List.rev !body_instrs in

      let body_defs = collect_defs body_instrs in

      let trip_opt = ref None in
      for j = hstart to hend do
        match arr.(j) with
        | Li (_, n) when n > 0 && n <= 4 ->
          trip_opt := Some n
        | _ -> ()
      done;

      match !trip_opt with
      | Some k when k <= 2 ->
        let tail_body = ref [] in
        for j = tstart to tend do tail_body := arr.(j) :: !tail_body done;
        let tail_body = List.rev !tail_body in
        let body_only = List.filter (fun i ->
          match i with Label _ | Bz _ | Bnz _ | Jmp _ -> false | _ -> true
        ) tail_body in

        let copies = ref [] in
        for _ = 1 to k do
          copies := (List.rev body_only) :: !copies
        done;
        for j = hstart to tend do remove.(j) <- true done;
        if hstart > 0 then
          insert.(hstart - 1) <- (List.flatten !copies |> List.rev) @ insert.(hstart - 1)

      | _ ->
        let body_tail = ref [] in
        for j = tstart to tend do body_tail := arr.(j) :: !body_tail done;
        let body_tail = List.rev !body_tail in
        let body_no_jmp = List.filter (function Jmp _ -> false | _ -> true) body_tail in
        let body_sz = List.length body_no_jmp in
        if body_sz >= 5 then begin
          let rmap = ref IMap.empty in
          ISet.iter (fun r ->
            let fresh = !next_vreg in
            incr next_vreg;
            rmap := IMap.add r fresh !rmap
          ) body_defs;
          let copy = List.map (rename_instr !rmap) body_no_jmp in
          insert.(tend - 1) <- (List.rev copy) @ insert.(tend - 1)
        end
    ) !loops;

    let result = ref [] in
    for i = Array.length arr - 1 downto 0 do
      if not remove.(i) then begin
        List.iter (fun instr -> result := instr :: !result) insert.(i);
        result := arr.(i) :: !result
      end
    done;
    { f with fir_body = !result }
  end

(* --- Driver for the local passes --- *)

let optimize_func_body (body : instr list) : instr list =
  let rec loop iter body =
    if iter >= max_iterations then body
    else
      let body' = body
        |> const_fold
        |> alg_simplify
        |> copy_prop
        |> strength_reduce
        |> dead_code_elim
        |> peephole
        |> remove_dead_after_jmp
      in
      if body' = body then body' else loop (iter + 1) body'
  in
  loop 0 body

(* --- CSE (basic-block-level) from incoming branch, adapted to use existing helpers --- *)

type expr_key =
  | KBinop of binop * value * value
  | KUnop  of uop   * value
  | KLi    of int
  | KLa    of string
  | KLw    of int             (* stack slot offset, Lw(0, off) only *)

let cse_func (f : func_ir) : func_ir =
  let tbl : (expr_key, vreg) Hashtbl.t = Hashtbl.create 64 in
  let invalidate_lw off =
    Hashtbl.filter_map_inplace
      (fun k v -> match k with KLw o when o = off -> None | _ -> Some v)
      tbl
  in
  let new_body =
    List.map (fun instr ->
      match instr with
      | Binop (rd, op, v1, v2) ->
        let key = KBinop (op, v1, v2) in
        (match Hashtbl.find_opt tbl key with
         | Some r -> Mov (rd, VReg r)
         | None   -> Hashtbl.replace tbl key rd; instr)
      | Unop (rd, op, v) ->
        let key = KUnop (op, v) in
        (match Hashtbl.find_opt tbl key with
         | Some r -> Mov (rd, VReg r)
         | None   -> Hashtbl.replace tbl key rd; instr)
      | Li (rd, n) ->
        let key = KLi n in
        (match Hashtbl.find_opt tbl key with
         | Some r -> Mov (rd, VReg r)
         | None   -> Hashtbl.replace tbl key rd; instr)
      | La (rd, name) ->
        let key = KLa name in
        (match Hashtbl.find_opt tbl key with
         | Some r -> Mov (rd, VReg r)
         | None   -> Hashtbl.replace tbl key rd; instr)
      | Lw (rd, 0, off) ->
        let key = KLw off in
        (match Hashtbl.find_opt tbl key with
         | Some r -> Mov (rd, VReg r)
         | None   -> Hashtbl.replace tbl key rd; instr)
      | Sw (0, off, _) ->
        invalidate_lw off; instr
      | Call _ | Jmp _ | Label _ ->
        Hashtbl.reset tbl; instr
      | _ -> instr
    ) f.fir_body
  in
  { f with fir_body = new_body }

(* --- Iterative DCE wrapper using the local dead_code_elim pass --- *)

let dce (f : func_ir) : func_ir =
  let rec loop body =
    let body' = dead_code_elim body in
    if List.length body' = List.length body then body' else loop body'
  in
  { f with fir_body = loop f.fir_body }

(* --- Combined optimize_func: run CSE -> local passes -> iterative DCE until convergence --- *)

let optimize_func (f : func_ir) : func_ir =
  let rec loop f =
    let f1 = cse_func f in
    let f2 = { f1 with fir_body = optimize_func_body f1.fir_body } in
    let f3 = dce f2 in
    if List.length f3.fir_body = List.length f.fir_body then f3 else loop f3
  in
  loop (unroll_func f)

let optimize_module (m : module_ir) : module_ir =
  { m with mir_functions = List.map optimize_func m.mir_functions }
