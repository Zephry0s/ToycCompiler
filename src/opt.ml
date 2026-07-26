open Ast
open Ir

let max_iterations = 5

module IntSet = Set.Make(struct type t = int let compare = compare end)

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

(* --- Pass 4: Dead local-store elimination --- *)

let remove_overwritten_stores_in_block (instrs : instr list) : instr list =
  let rec scan seen_store acc = function
    | [] -> acc
    | Sw (0, off, _) :: rest when IntSet.mem off seen_store ->
      scan seen_store acc rest
    | (Sw (0, off, _) as instr) :: rest ->
      scan (IntSet.add off seen_store) (instr :: acc) rest
    | (Lw (_, 0, off) as instr) :: rest ->
      scan (IntSet.remove off seen_store) (instr :: acc) rest
    | instr :: rest ->
      scan seen_store (instr :: acc) rest
  in
  scan IntSet.empty [] (List.rev instrs)

let dead_store_elim (instrs : instr list) : instr list =
  let loaded_slots =
    List.fold_left (fun slots -> function
      | Lw (_, 0, off) -> IntSet.add off slots
      | _ -> slots
    ) IntSet.empty instrs
  in
  instrs
  |> List.filter (function
       | Sw (0, off, _) -> IntSet.mem off loaded_slots
       | _ -> true)
  |> split_blocks
  |> List.map remove_overwritten_stores_in_block
  |> List.fold_left (@) []

(* --- Pass 5: Dead Code Elimination --- *)

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

(* --- Pass 6: Peephole --- *)

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

(* --- Pass 7: Dead code after unconditional jumps --- *)

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
 * Safe loop and recursion optimizations
 * ================================================================ *)

let find_max_vreg (body : instr list) : int =
  let max_r = ref 0 in
  let check_reg r = if r > !max_r then max_r := r in
  let check_val = function VReg r -> check_reg r | VImm _ -> () in
  List.iter (function
    | Binop (rd, _, v1, v2) -> check_reg rd; check_val v1; check_val v2
    | Unop (rd, _, v) | Mov (rd, v) -> check_reg rd; check_val v
    | Li (rd, _) | La (rd, _) -> check_reg rd
    | Lw (rd, base, _) -> check_reg rd; check_reg base
    | Sw (base, _, v) -> check_reg base; check_val v
    | Call (rd, _, args) -> check_reg rd; List.iter check_val args
    | Ret (Some v) | Bz (v, _) | Bnz (v, _) -> check_val v
    | Ret None | Jmp _ | Label _ -> ()
  ) body;
  !max_r

(* Direct self tail calls reuse the current frame.  Arguments have already
   been evaluated into vregs, so storing them to parameter slots implements
   the required parallel assignment before jumping back to the body entry. *)
let tail_rec_elim (f : func_ir) : func_ir =
  let param_count = List.length f.fir_params in
  let is_tail_call = function
    | Call (rd, name, args) :: Ret (Some (VReg result)) :: _
      when name = f.fir_name && rd = result &&
           List.length args = param_count -> true
    | Call (_, name, args) :: Ret None :: _
      when name = f.fir_name && List.length args = param_count -> true
    | _ -> false
  in
  let rec contains_tail_call = function
    | [] -> false
    | (_ :: rest as instrs) ->
      is_tail_call instrs || contains_tail_call rest
  in
  if not (contains_tail_call f.fir_body) then f
  else
    let rec split_param_stores params body acc =
      match params, body with
      | [], _ -> Some (List.rev acc, body)
      | (_, off) :: params_rest,
        (Sw (0, actual_off, VReg _) as store) :: body_rest
        when off = actual_off ->
          split_param_stores params_rest body_rest (store :: acc)
      | _ -> None
    in
    match split_param_stores f.fir_params f.fir_body [] with
    | None -> f
    | Some (prologue, body) ->
      let entry_label = ".tailrec_" ^ f.fir_name in
      let stores_for args =
        List.map2 (fun (_, off) arg -> Sw (0, off, arg)) f.fir_params args
      in
      let rec rewrite = function
        | Call (rd, name, args) :: Ret (Some (VReg result)) :: rest
          when name = f.fir_name && rd = result &&
               List.length args = param_count ->
            stores_for args @ Jmp entry_label :: rewrite rest
        | Call (_, name, args) :: Ret None :: rest
          when name = f.fir_name && List.length args = param_count ->
            stores_for args @ Jmp entry_label :: rewrite rest
        | instr :: rest -> instr :: rewrite rest
        | [] -> []
      in
      { f with fir_body = prologue @ Label entry_label :: rewrite body }

let starts_with prefix s =
  let prefix_len = String.length prefix in
  String.length s >= prefix_len &&
  String.sub s 0 prefix_len = prefix

let is_while_header label =
  starts_with ".while" label && not (starts_with ".while_end" label)

let is_while_end label =
  starts_with ".while_end" label

let take n xs =
  let rec loop left acc = function
    | _ when left = 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: rest -> loop (left - 1) (x :: acc) rest
  in
  loop n [] xs

(* Tail-recursive parameter slots are private to the current frame.  Cache the
   frequently read ones after the initial parameter stores; tail backedges
   update the cache directly and skip the one-time loads. *)
let cache_tailrec_params (f : func_ir) : func_ir =
  let entry_label = ".tailrec_" ^ f.fir_name in
  let arr = Array.of_list f.fir_body in
  let entry_idx = ref None in
  Array.iteri (fun idx -> function
    | Label label when label = entry_label -> entry_idx := Some idx
    | _ -> ()
  ) arr;
  match !entry_idx with
  | None -> f
  | Some label_idx ->
    let param_offsets =
      List.fold_left (fun offsets (_, off) -> off :: offsets)
        [] f.fir_params
    in
    let read_counts = Hashtbl.create (List.length param_offsets) in
    for idx = label_idx + 1 to Array.length arr - 1 do
      match arr.(idx) with
      | Lw (_, 0, off) when List.mem off param_offsets ->
        let old =
          match Hashtbl.find_opt read_counts off with
          | Some count -> count
          | None -> 0
        in
        Hashtbl.replace read_counts off (old + 1)
      | _ -> ()
    done;
    let selected_offsets =
      Hashtbl.to_seq read_counts
      |> List.of_seq
      |> List.sort (fun (off1, count1) (off2, count2) ->
           let by_count = compare count2 count1 in
           if by_count <> 0 then by_count else compare off1 off2)
      |> take 8
      |> List.map fst
    in
    if selected_offsets = [] then f
    else
      let next_vreg = ref (find_max_vreg f.fir_body + 1) in
      let cache_for_slot = Hashtbl.create (List.length selected_offsets) in
      List.iter (fun off ->
        Hashtbl.add cache_for_slot off !next_vreg;
        incr next_vreg
      ) selected_offsets;
      let loads =
        List.map (fun off ->
          Lw (Hashtbl.find cache_for_slot off, 0, off)
        ) selected_offsets
      in
      let result = ref [] in
      Array.iteri (fun idx instr ->
        if idx = label_idx then
          List.iter (fun load -> result := load :: !result) loads;
        let rewritten =
          if idx <= label_idx then instr
          else
            match instr with
            | Lw (rd, 0, off) when Hashtbl.mem cache_for_slot off ->
              Mov (rd, VReg (Hashtbl.find cache_for_slot off))
            | Sw (0, off, value) when Hashtbl.mem cache_for_slot off ->
              Mov (Hashtbl.find cache_for_slot off, value)
            | _ -> instr
        in
        result := rewritten :: !result
      ) arr;
      { f with fir_body = List.rev !result }

(* Keep frequently accessed local stack slots in virtual registers inside
   innermost structured while loops.  The original control flow is unchanged:
   slots are loaded before the header and flushed immediately after the exit
   label, which also covers break edges. *)
let cache_loop_slots (f : func_ir) : func_ir =
  let arr = Array.of_list f.fir_body in
  let n = Array.length arr in
  if n = 0 then f
  else
    let label_pos = Hashtbl.create 32 in
    Array.iteri (fun idx -> function
      | Label label -> Hashtbl.replace label_pos label idx
      | _ -> ()
    ) arr;
    let loops = ref [] in
    Array.iteri (fun header_idx -> function
      | Label header_label when is_while_header header_label ->
        let exit_idx = ref None in
        let cursor = ref (header_idx + 1) in
        while !cursor < n && !exit_idx = None do
          (match arr.(!cursor) with
           | Bz (_, exit_label) when is_while_end exit_label ->
             (match Hashtbl.find_opt label_pos exit_label with
              | Some idx when idx > !cursor -> exit_idx := Some idx
              | _ -> ())
           | _ -> ());
          incr cursor
        done;
        (match !exit_idx with
         | Some idx -> loops := (header_idx, idx) :: !loops
         | None -> ())
      | _ -> ()
    ) arr;
    let loops = !loops in
    let has_only_local_edges (header_idx, exit_idx) =
      let target_is_local label =
        match Hashtbl.find_opt label_pos label with
        | Some idx -> idx >= header_idx && idx <= exit_idx
        | None -> false
      in
      let local = ref true in
      for idx = header_idx + 1 to exit_idx - 1 do
        match arr.(idx) with
        | Jmp label | Bz (_, label) | Bnz (_, label) ->
          if not (target_is_local label) then local := false
        | _ -> ()
      done;
      !local
    in
    let innermost_loops =
      List.filter (fun (header_idx, exit_idx) ->
        has_only_local_edges (header_idx, exit_idx) &&
        not (List.exists (fun (inner_header, inner_exit) ->
          header_idx < inner_header && inner_exit < exit_idx
        ) loops)
      ) loops
    in
    if innermost_loops = [] then f
    else
      let next_vreg = ref (find_max_vreg f.fir_body + 1) in
      let rewritten = Array.copy arr in
      let before = Array.make n [] in
      let after = Array.make n [] in
      List.iter (fun (header_idx, exit_idx) ->
        let access_counts = Hashtbl.create 16 in
        let note off is_read =
          let reads, total =
            match Hashtbl.find_opt access_counts off with
            | Some counts -> counts
            | None -> (0, 0)
          in
          Hashtbl.replace access_counts off
            (reads + (if is_read then 1 else 0), total + 1)
        in
        for idx = header_idx + 1 to exit_idx - 1 do
          match arr.(idx) with
          | Lw (_, 0, off) -> note off true
          | Sw (0, off, _) -> note off false
          | _ -> ()
        done;
        let selected_slots =
          Hashtbl.to_seq access_counts
          |> List.of_seq
          |> List.filter (fun (_, (reads, _)) -> reads > 0)
          |> List.sort (fun (off1, (_, total1)) (off2, (_, total2)) ->
               let by_count = compare total2 total1 in
               if by_count <> 0 then by_count else compare off1 off2)
          |> take 8
        in
        let cache_for_slot = Hashtbl.create (List.length selected_slots) in
        List.iter (fun (off, _) ->
          let cache = !next_vreg in
          incr next_vreg;
          Hashtbl.add cache_for_slot off cache
        ) selected_slots;
        let loads =
          List.map (fun (off, _) ->
            Lw (Hashtbl.find cache_for_slot off, 0, off)
          ) selected_slots
        in
        let stores =
          List.map (fun (off, _) ->
            Sw (0, off, VReg (Hashtbl.find cache_for_slot off))
          ) selected_slots
        in
        before.(header_idx) <- loads @ before.(header_idx);
        after.(exit_idx) <- stores @ after.(exit_idx);
        for idx = header_idx + 1 to exit_idx - 1 do
          rewritten.(idx) <-
            match rewritten.(idx) with
            | Lw (rd, 0, off) when Hashtbl.mem cache_for_slot off ->
              Mov (rd, VReg (Hashtbl.find cache_for_slot off))
            | Sw (0, off, value) when Hashtbl.mem cache_for_slot off ->
              Mov (Hashtbl.find cache_for_slot off, value)
            | instr -> instr
        done
      ) innermost_loops;
      let result = ref [] in
      let append instrs =
        List.iter (fun instr -> result := instr :: !result) instrs
      in
      for idx = 0 to n - 1 do
        append before.(idx);
        result := rewritten.(idx) :: !result;
        append after.(idx)
      done;
      { f with fir_body = List.rev !result }

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
        |> dead_store_elim
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
        invalidate_lw off;
        (match instr with
         | Sw (_, _, VReg r) -> Hashtbl.replace tbl (KLw off) r
         | _ -> ());
        instr
      | Call _ | Jmp _ | Bz _ | Bnz _ | Ret _ | Label _ ->
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
  let rec loop iter f =
    if iter >= max_iterations then f
    else
    let f1 = cse_func f in
    let f2 = { f1 with fir_body = optimize_func_body f1.fir_body } in
    let f3 = dce f2 in
    if f3.fir_body = f.fir_body then f3 else loop (iter + 1) f3
  in
  f
  |> tail_rec_elim
  |> loop 0
  |> cache_tailrec_params
  |> cache_loop_slots

let optimize_module (m : module_ir) : module_ir =
  { m with mir_functions = List.map optimize_func m.mir_functions }
