open Ast
open Ir

let max_iterations = 5

module IntSet = Set.Make(struct type t = int let compare = compare end)
module IntMap = Map.Make(struct type t = int let compare = compare end)
module StringMap = Map.Make(String)

(* --- Utility --- *)

let eval_binop = eval_i32_binop

let eval_uop = eval_i32_uop

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

(* --- Shared control-flow graph --- *)

type cfg_block = {
  cb_id    : int;
  cb_start : int;
  cb_end   : int;
  cb_succs : int list;
  cb_preds : int list;
}

type cfg = {
  cfg_instrs : instr array;
  cfg_blocks : cfg_block array;
}

let dedup_ints values =
  List.fold_left (fun result value ->
    if List.mem value result then result else result @ [value]
  ) [] values

let build_cfg (instrs : instr list) : cfg =
  let arr = Array.of_list instrs in
  let n = Array.length arr in
  if n = 0 then { cfg_instrs = arr; cfg_blocks = [||] }
  else begin
    let starts = Array.make n false in
    starts.(0) <- true;
    for idx = 0 to n - 1 do
      (match arr.(idx) with
       | Label _ -> starts.(idx) <- true
       | _ -> ());
      (match arr.(idx) with
       | Jmp _ | Bz _ | Bnz _ | Ret _ ->
         if idx + 1 < n then starts.(idx + 1) <- true
       | _ -> ())
    done;
    let ranges = ref [] in
    let idx = ref 0 in
    while !idx < n do
      let first = !idx in
      let next = ref (first + 1) in
      while !next < n && not starts.(!next) do
        incr next
      done;
      ranges := (first, !next - 1) :: !ranges;
      idx := !next
    done;
    let ranges = Array.of_list (List.rev !ranges) in
    let label_blocks = ref StringMap.empty in
    Array.iteri (fun block_id (first, _) ->
      match arr.(first) with
      | Label label ->
        label_blocks := StringMap.add label block_id !label_blocks
      | _ -> ()
    ) ranges;
    let succs = Array.make (Array.length ranges) [] in
    Array.iteri (fun block_id (_, last) ->
      let target label =
        match StringMap.find_opt label !label_blocks with
        | Some target_id -> [target_id]
        | None -> []
      in
      let fallthrough =
        if block_id + 1 < Array.length ranges then [block_id + 1] else []
      in
      succs.(block_id) <-
        dedup_ints
          (match arr.(last) with
           | Jmp label -> target label
           | Bz (_, label) | Bnz (_, label) ->
             target label @ fallthrough
           | Ret _ -> []
           | _ -> fallthrough)
    ) ranges;
    let preds = Array.make (Array.length ranges) [] in
    Array.iteri (fun source targets ->
      List.iter (fun target ->
        preds.(target) <- source :: preds.(target)
      ) targets
    ) succs;
    let blocks =
      Array.mapi (fun block_id (first, last) ->
        { cb_id = block_id;
          cb_start = first;
          cb_end = last;
          cb_succs = succs.(block_id);
          cb_preds = List.rev preds.(block_id) }
      ) ranges
    in
    { cfg_instrs = arr; cfg_blocks = blocks }
  end

let reachable_blocks cfg =
  let count = Array.length cfg.cfg_blocks in
  let reachable = Array.make count false in
  if count > 0 then begin
    let worklist = Queue.create () in
    reachable.(0) <- true;
    Queue.add 0 worklist;
    while not (Queue.is_empty worklist) do
      let block_id = Queue.take worklist in
      List.iter (fun successor ->
        if not reachable.(successor) then begin
          reachable.(successor) <- true;
          Queue.add successor worklist
        end
      ) cfg.cfg_blocks.(block_id).cb_succs
    done
  end;
  reachable

let remove_unreachable_blocks (instrs : instr list) : instr list =
  let cfg = build_cfg instrs in
  let reachable = reachable_blocks cfg in
  let result = ref [] in
  Array.iteri (fun block_id block ->
    if reachable.(block_id) then
      for idx = block.cb_start to block.cb_end do
        result := cfg.cfg_instrs.(idx) :: !result
      done
  ) cfg.cfg_blocks;
  List.rev !result

(* --- Global constant propagation over CFG blocks --- *)

type const_state = {
  cs_regs  : int IntMap.t;
  cs_slots : int IntMap.t;
}

let empty_const_state = {
  cs_regs = IntMap.empty;
  cs_slots = IntMap.empty;
}

let equal_const_state lhs rhs =
  IntMap.equal ( = ) lhs.cs_regs rhs.cs_regs &&
  IntMap.equal ( = ) lhs.cs_slots rhs.cs_slots

let intersect_constants lhs rhs =
  IntMap.merge (fun _ left right ->
    match left, right with
    | Some a, Some b when a = b -> Some a
    | _ -> None
  ) lhs rhs

let meet_const_states = function
  | [] -> empty_const_state
  | first :: rest ->
    List.fold_left (fun state incoming ->
      { cs_regs = intersect_constants state.cs_regs incoming.cs_regs;
        cs_slots = intersect_constants state.cs_slots incoming.cs_slots }
    ) first rest

let constant_of_value state = function
  | VImm value -> Some (normalize_i32 value)
  | VReg 0 -> None
  | VReg reg -> IntMap.find_opt reg state.cs_regs

let set_reg_constant state reg value =
  { state with
    cs_regs = IntMap.add reg (normalize_i32 value) state.cs_regs }

let forget_reg state reg =
  { state with cs_regs = IntMap.remove reg state.cs_regs }

let transfer_const state instr =
  let define_from_value rd value =
    match constant_of_value state value with
    | Some constant -> set_reg_constant state rd constant
    | None -> forget_reg state rd
  in
  match instr with
  | Li (rd, value) -> set_reg_constant state rd value
  | Mov (rd, value) -> define_from_value rd value
  | Unop (rd, op, value) ->
    (match constant_of_value state value with
     | Some constant -> set_reg_constant state rd (eval_uop op constant)
     | None -> forget_reg state rd)
  | Binop (rd, op, left, right) ->
    (match constant_of_value state left, constant_of_value state right with
     | Some lhs, Some rhs
       when not ((op = Div || op = Mod) && normalize_i32 rhs = 0) ->
       set_reg_constant state rd (eval_binop op lhs rhs)
     | _ -> forget_reg state rd)
  | Lw (rd, 0, offset) ->
    (match IntMap.find_opt offset state.cs_slots with
     | Some constant -> set_reg_constant state rd constant
     | None -> forget_reg state rd)
  | Lw (rd, _, _) | La (rd, _) | Call (rd, _, _) ->
    forget_reg state rd
  | Sw (0, offset, value) ->
    let slots =
      match constant_of_value state value with
      | Some constant -> IntMap.add offset constant state.cs_slots
      | None -> IntMap.remove offset state.cs_slots
    in
    { state with cs_slots = slots }
  | Sw _ | Ret _ | Jmp _ | Bz _ | Bnz _ | Label _ -> state

let rewrite_with_constants state instr =
  let rewrite_value value =
    match constant_of_value state value with
    | Some constant -> VImm constant
    | None -> value
  in
  match instr with
  | Binop (rd, op, left, right) ->
    Binop (rd, op, rewrite_value left, rewrite_value right)
  | Unop (rd, op, value) ->
    Unop (rd, op, rewrite_value value)
  | Mov (rd, value) ->
    Mov (rd, rewrite_value value)
  | Lw (rd, 0, offset) ->
    (match IntMap.find_opt offset state.cs_slots with
     | Some constant -> Li (rd, constant)
     | None -> instr)
  | Sw (base, offset, value) ->
    Sw (base, offset, rewrite_value value)
  | Call (rd, name, args) ->
    Call (rd, name, List.map rewrite_value args)
  | Ret (Some value) ->
    Ret (Some (rewrite_value value))
  | Bz (value, label) ->
    Bz (rewrite_value value, label)
  | Bnz (value, label) ->
    Bnz (rewrite_value value, label)
  | Li _ | Lw _ | La _ | Ret None | Jmp _ | Label _ -> instr

let global_const_prop (f : func_ir) : func_ir =
  let cfg = build_cfg f.fir_body in
  let block_count = Array.length cfg.cfg_blocks in
  if block_count = 0 then f
  else begin
    let reachable = reachable_blocks cfg in
    let in_states = Array.make block_count None in
    let out_states = Array.make block_count None in
    let changed = ref true in
    while !changed do
      changed := false;
      for block_id = 0 to block_count - 1 do
        if reachable.(block_id) then begin
          let block = cfg.cfg_blocks.(block_id) in
          let predecessor_states =
            List.filter_map (fun predecessor ->
              out_states.(predecessor)
            ) block.cb_preds
          in
          let incoming =
            if block_id = 0 then Some empty_const_state
            else
              match predecessor_states with
              | [] -> None
              | states -> Some (meet_const_states states)
          in
          let outgoing =
            match incoming with
            | None -> None
            | Some state ->
              let state = ref state in
              for idx = block.cb_start to block.cb_end do
                state := transfer_const !state cfg.cfg_instrs.(idx)
              done;
              Some !state
          in
          let state_option_equal left right =
            match left, right with
            | None, None -> true
            | Some a, Some b -> equal_const_state a b
            | _ -> false
          in
          if not (state_option_equal in_states.(block_id) incoming) ||
             not (state_option_equal out_states.(block_id) outgoing) then begin
            in_states.(block_id) <- incoming;
            out_states.(block_id) <- outgoing;
            changed := true
          end
        end
      done
    done;
    let rewritten = Array.copy cfg.cfg_instrs in
    Array.iteri (fun block_id block ->
      match in_states.(block_id) with
      | None -> ()
      | Some incoming ->
        let state = ref incoming in
        for idx = block.cb_start to block.cb_end do
          let instr = rewrite_with_constants !state rewritten.(idx) in
          rewritten.(idx) <- instr;
          state := transfer_const !state instr
        done
    ) cfg.cfg_blocks;
    { f with fir_body = Array.to_list rewritten }
  end

(* CFG-wide copy propagation.  This is deliberately separate from constant
   propagation: CSE and slot promotion create register-to-register copies
   whose values remain useful across block boundaries even when they are not
   constants.  Meet keeps only facts that are identical on every incoming
   path, matching LLVM's conservative value propagation at joins. *)
let global_copy_prop (f : func_ir) : func_ir =
  let cfg = build_cfg f.fir_body in
  let block_count = Array.length cfg.cfg_blocks in
  if block_count = 0 then f
  else
    let rec resolve depth state = function
      | VImm _ as value -> value
      | VReg 0 as value -> value
      | VReg reg as value ->
        if depth >= 16 then value
        else
          match IntMap.find_opt reg state with
          | Some replacement -> resolve (depth + 1) state replacement
          | None -> value
    in
    let kill state reg =
      IntMap.filter (fun key value ->
        key <> reg &&
        match resolve 0 state value with
        | VReg source -> source <> reg
        | VImm _ -> true
      ) state
    in
    let rewrite state instr =
      let value = resolve 0 state in
      let base reg =
        match value (VReg reg) with VReg mapped -> mapped | VImm _ -> reg
      in
      match instr with
      | Binop (rd, op, left, right) ->
        Binop (rd, op, value left, value right)
      | Unop (rd, op, operand) ->
        Unop (rd, op, value operand)
      | Mov (rd, operand) -> Mov (rd, value operand)
      | Lw (rd, address, offset) -> Lw (rd, base address, offset)
      | Sw (address, offset, operand) ->
        Sw (base address, offset, value operand)
      | Call (rd, name, args) ->
        Call (rd, name, List.map value args)
      | Ret (Some operand) -> Ret (Some (value operand))
      | Bz (operand, label) -> Bz (value operand, label)
      | Bnz (operand, label) -> Bnz (value operand, label)
      | Li _ | La _ | Ret None | Jmp _ | Label _ -> instr
    in
    let transfer state instr =
      match def_vreg instr with
      | None -> state
      | Some rd ->
        let state = kill state rd in
        (match instr with
         | Mov (_, operand) ->
           let operand = resolve 0 state operand in
           (match operand with
            | VReg source when source = rd -> state
            | _ -> IntMap.add rd operand state)
         (* Constants are handled by [global_const_prop].  Keeping them out
            of this copy-only lattice is important for loop-invariant [li]
            instructions: a backedge must not turn a deliberately hoisted
            register value back into an immediate in the hot block. *)
         | Li _ -> state
         | _ -> state)
    in
    let meet states =
      match states with
      | [] -> IntMap.empty
      | first :: rest ->
        List.fold_left (fun common incoming ->
          IntMap.merge (fun _ left right ->
            match left, right with
            | Some a, Some b when a = b -> Some a
            | _ -> None
          ) common incoming
        ) first rest
    in
    let reachable = reachable_blocks cfg in
    let in_states = Array.make block_count None in
    let out_states = Array.make block_count None in
    let option_equal left right =
      match left, right with
      | None, None -> true
      | Some lhs, Some rhs -> IntMap.equal ( = ) lhs rhs
      | _ -> false
    in
    let changed = ref true in
    while !changed do
      changed := false;
      for block_id = 0 to block_count - 1 do
        if reachable.(block_id) then begin
          let block = cfg.cfg_blocks.(block_id) in
          let predecessor_states =
            List.filter_map (fun predecessor -> out_states.(predecessor))
              block.cb_preds
          in
          let incoming =
            if block_id = 0 then Some IntMap.empty
            else
              match predecessor_states with
              | [] -> None
              | states -> Some (meet states)
          in
          let outgoing =
            match incoming with
            | None -> None
            | Some initial ->
              let state = ref initial in
              for idx = block.cb_start to block.cb_end do
                let instr = rewrite !state cfg.cfg_instrs.(idx) in
                state := transfer !state instr
              done;
              Some !state
          in
          if not (option_equal in_states.(block_id) incoming) ||
             not (option_equal out_states.(block_id) outgoing) then begin
            in_states.(block_id) <- incoming;
            out_states.(block_id) <- outgoing;
            changed := true
          end
        end
      done
    done;
    let rewritten = Array.copy cfg.cfg_instrs in
    Array.iteri (fun block_id block ->
      match in_states.(block_id) with
      | None -> ()
      | Some incoming ->
        let state = ref incoming in
        for idx = block.cb_start to block.cb_end do
          let instr = rewrite !state rewritten.(idx) in
          rewritten.(idx) <- instr;
          state := transfer !state instr
        done
    ) cfg.cfg_blocks;
    { f with fir_body = Array.to_list rewritten }

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
       | Div | Mod when normalize_i32 b = 0 -> i
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
    | Binop (rd, Mul, v, VImm (-1))
    | Binop (rd, Mul, VImm (-1), v) -> Unop (rd, Neg, v)
    | Binop (rd, Mul, _, VImm 0) | Binop (rd, Mul, VImm 0, _) -> Li (rd, 0)
    | Binop (rd, Div, v, VImm 1) -> Mov (rd, v)
    | Binop (rd, Div, v, VImm (-1)) -> Unop (rd, Neg, v)
    | Binop (rd, Div, VImm 0, VImm n) when n <> 0 -> Li (rd, 0)
    | Binop (rd, Mod, _, VImm 1) -> Li (rd, 0)
    | Binop (rd, Mod, _, VImm (-1)) -> Li (rd, 0)
    | Binop (rd, Mod, VImm 0, VImm n) when n <> 0 -> Li (rd, 0)
    | Binop (rd, Sub, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 0)
    | Binop (rd, Eq, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 1)
    | Binop (rd, Neq, VReg r1, VReg r2) when r1 = r2 -> Li (rd, 0)
    | Binop (rd, (Le | Ge), VReg r1, VReg r2) when r1 = r2 -> Li (rd, 1)
    | Binop (rd, (Lt | Gt), VReg r1, VReg r2) when r1 = r2 -> Li (rd, 0)
    | _ -> i
  ) instrs

(* --- Pass 2.5: Strength Reduction --- *)

let strength_reduce (instrs : instr list) : instr list =
  List.map (fun i -> match i with
    | Binop (rd, Mul, v, VImm 2) | Binop (rd, Mul, VImm 2, v) ->
      Binop (rd, Add, v, v)
    | _ -> i
  ) instrs

(* Fold one-use arithmetic chains in the style of LLVM InstCombine.  Keeping
   the rule local avoids reassociating potentially trapping division while
   still exposing a single target immediate for common [x + c1 + c2] trees. *)
let combine_constant_chains (instrs : instr list) : instr list =
  let use_counts = Hashtbl.create 64 in
  List.iter (fun instr ->
    List.iter (fun reg ->
      if reg <> 0 then begin
        let old =
          match Hashtbl.find_opt use_counts reg with Some n -> n | None -> 0
        in
        Hashtbl.replace use_counts reg (old + 1)
      end
    ) (src_vregs instr)
  ) instrs;
  let used_once reg = Hashtbl.find_opt use_counts reg = Some 1 in
  let additive_base = function
    | Binop (rd, Add, base, VImm constant)
    | Binop (rd, Add, VImm constant, base) ->
      Some (rd, base, normalize_i32 constant)
    | Binop (rd, Sub, base, VImm constant) ->
      Some (rd, base, eval_uop Neg constant)
    | _ -> None
  in
  let additive_use reg = function
    | Binop (rd, Add, VReg source, VImm constant)
    | Binop (rd, Add, VImm constant, VReg source)
      when source = reg ->
      Some (rd, normalize_i32 constant)
    | Binop (rd, Sub, VReg source, VImm constant)
      when source = reg ->
      Some (rd, eval_uop Neg constant)
    | _ -> None
  in
  let rec scan acc = function
    | first :: second :: rest ->
      (match additive_base first with
       | Some (temporary, base, first_constant) when used_once temporary ->
         (match additive_use temporary second with
          | Some (result, second_constant) ->
            let combined = eval_binop Add first_constant second_constant in
            let replacement =
              if combined = 0 then Mov (result, base)
              else Binop (result, Add, base, VImm combined)
            in
            scan (replacement :: acc) rest
          | None -> scan (first :: acc) (second :: rest))
       | _ ->
         (match first, second with
          | Binop (temporary, Mul, base, VImm first_constant),
            Binop (result, Mul, VReg source, VImm second_constant)
            when source = temporary && used_once temporary ->
            let combined = eval_binop Mul first_constant second_constant in
            scan (Binop (result, Mul, base, VImm combined) :: acc) rest
          | _ -> scan (first :: acc) (second :: rest)))
    | remaining -> List.rev_append acc remaining
  in
  scan [] instrs

(* --- Pass 3: Copy Propagation --- *)

let copy_prop_block (instrs : instr list) : instr list =
  let subst = Hashtbl.create 16 in
  let rec value_depends_on depth target = function
    | VImm _ -> false
    | VReg reg when reg = target -> true
    | VReg reg ->
      if depth > 16 then true
      else
        match Hashtbl.find_opt subst reg with
        | Some value -> value_depends_on (depth + 1) target value
        | None -> false
  in
  let invalidate_definition rd =
    Hashtbl.filter_map_inplace (fun reg value ->
      if reg = rd || value_depends_on 0 rd value then None
      else Some value
    ) subst
  in
  let changed = ref false in
  let result = List.map (fun i ->
    let i' = subst_instr subst i in
    if i' <> i then changed := true;
    (match def_vreg i' with
     | Some rd ->
       invalidate_definition rd;
       (match i' with
        | Mov (_, VReg source) when source = rd -> ()
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

(* Backward memory liveness for non-escaping local slots.  A store is dead
   when no path from it reads the slot before another store.  This is the
   MemorySSA-style whole-CFG counterpart of the older basic-block overwrite
   scan; function exit observes no local slots and calls cannot alias them. *)
let global_dead_store_elim (instrs : instr list) : instr list =
  let cfg = build_cfg instrs in
  let block_count = Array.length cfg.cfg_blocks in
  if block_count = 0 then instrs
  else
    let uses = Array.make block_count IntSet.empty in
    let defs = Array.make block_count IntSet.empty in
    Array.iteri (fun block_id block ->
      let defined = ref IntSet.empty in
      for idx = block.cb_start to block.cb_end do
        match cfg.cfg_instrs.(idx) with
        | Lw (_, 0, offset) ->
          if not (IntSet.mem offset !defined) then
            uses.(block_id) <- IntSet.add offset uses.(block_id)
        | Sw (0, offset, _) ->
          defined := IntSet.add offset !defined;
          defs.(block_id) <- IntSet.add offset defs.(block_id)
        | _ -> ()
      done
    ) cfg.cfg_blocks;
    let live_in = Array.make block_count IntSet.empty in
    let live_out = Array.make block_count IntSet.empty in
    let changed = ref true in
    while !changed do
      changed := false;
      for block_id = block_count - 1 downto 0 do
        let outgoing =
          List.fold_left (fun live successor ->
            IntSet.union live live_in.(successor)
          ) IntSet.empty cfg.cfg_blocks.(block_id).cb_succs
        in
        let incoming =
          IntSet.union uses.(block_id)
            (IntSet.diff outgoing defs.(block_id))
        in
        if not (IntSet.equal outgoing live_out.(block_id)) ||
           not (IntSet.equal incoming live_in.(block_id)) then begin
          live_out.(block_id) <- outgoing;
          live_in.(block_id) <- incoming;
          changed := true
        end
      done
    done;
    let keep = Array.make (Array.length cfg.cfg_instrs) true in
    Array.iteri (fun block_id block ->
      let live = ref live_out.(block_id) in
      for idx = block.cb_end downto block.cb_start do
        match cfg.cfg_instrs.(idx) with
        | Lw (_, 0, offset) ->
          live := IntSet.add offset !live
        | Sw (0, offset, _) ->
          if IntSet.mem offset !live then
            live := IntSet.remove offset !live
          else
            keep.(idx) <- false
        | _ -> ()
      done
    ) cfg.cfg_blocks;
    let result = ref [] in
    Array.iteri (fun idx instr ->
      if keep.(idx) then result := instr :: !result
    ) cfg.cfg_instrs;
    List.rev !result

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

let remove_unused_labels (instrs : instr list) : instr list =
  let targets =
    List.fold_left (fun labels -> function
      | Jmp label | Bz (_, label) | Bnz (_, label) ->
        StringMap.add label () labels
      | _ -> labels
    ) StringMap.empty instrs
  in
  List.filter (function
    | Label label -> StringMap.mem label targets
    | _ -> true
  ) instrs

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

(* Reuse a dominating quotient for a remainder with identical operands:
     q = x / C; r = x % C
   becomes
     q = x / C; product = q * C; r = x - product.
   LLVM performs the analogous div/rem pairing during value combining.  The
   rewrite is local to a basic block and invalidates entries on mutable-vreg
   redefinitions, so it is also safe after register-style slot promotion. *)
let combine_div_rem (body : instr list) : instr list =
  let next_vreg = ref (find_max_vreg body + 1) in
  let rewrite_block block =
    let quotients = Hashtbl.create 16 in
    let invalidate reg =
      Hashtbl.filter_map_inplace (fun (value, _) quotient ->
        let value_uses_reg =
          match value with VReg source -> source = reg | VImm _ -> false
        in
        if quotient = reg || value_uses_reg then None else Some quotient
      ) quotients
    in
    let result = ref [] in
    let append instr = result := instr :: !result in
    List.iter (fun instr ->
      (match def_vreg instr with Some reg -> invalidate reg | None -> ());
      match instr with
      | Binop (rd, Div, dividend, VImm divisor)
        when normalize_i32 divisor <> 0 ->
        append instr;
        Hashtbl.replace quotients
          (dividend, normalize_i32 divisor) rd
      | Binop (rd, Mod, dividend, VImm divisor)
        when normalize_i32 divisor <> 0 ->
        (match Hashtbl.find_opt quotients
                 (dividend, normalize_i32 divisor) with
         | Some quotient ->
           let product = !next_vreg in
           incr next_vreg;
           append (Binop (product, Mul, VReg quotient,
                     VImm (normalize_i32 divisor)));
           append (Binop (rd, Sub, dividend, VReg product))
         | None -> append instr)
      | _ -> append instr
    ) block;
    List.rev !result
  in
  body
  |> split_blocks
  |> List.map rewrite_block
  |> List.fold_left (@) []

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

let ends_with suffix s =
  let suffix_len = String.length suffix in
  let length = String.length s in
  length >= suffix_len &&
  String.sub s (length - suffix_len) suffix_len = suffix

let is_while_header label =
  starts_with ".while" label && not (starts_with ".while_end" label)

let is_while_end label =
  starts_with ".while_end" label

let find_while_loops (arr : instr array) =
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
      while !cursor < Array.length arr && !exit_idx = None do
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
  (label_pos, List.rev !loops)

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

let fits_i12 value =
  value >= -2048 && value <= 2047

let positive_power_of_two value =
  value > 0 && value land (value - 1) = 0

let signed_power_of_two value =
  let value = normalize_i32 value in
  let magnitude = if value < 0 then -value else value in
  positive_power_of_two magnitude

let cheap_multiply_constant value =
  let value = normalize_i32 value in
  let magnitude = if value < 0 then -value else value in
  magnitude > 1 &&
  (positive_power_of_two magnitude ||
   positive_power_of_two (magnitude - 1) ||
   positive_power_of_two (magnitude + 1))

(* Constants that require a temporary register in the final RV32 sequence
   should not be materialized on every hot-loop iteration. *)
let materialize_loop_constants (f : func_ir) : func_ir =
  let arr = Array.of_list f.fir_body in
  let n = Array.length arr in
  if n = 0 then f
  else
    let _, loops = find_while_loops arr in
    if loops = [] then f
    else begin
      let next_vreg = ref (find_max_vreg f.fir_body + 1) in
      let before = Array.make n [] in
      let is_compare_op = function
        | Eq | Neq | Lt | Gt | Le | Ge -> true
        | Add | Sub | Mul | Div | Mod | And | Or -> false
      in
      let feeds_branch idx rd =
        idx + 1 < n &&
        match arr.(idx + 1) with
        | Bz (VReg reg, _) | Bnz (VReg reg, _) -> reg = rd
        | _ -> false
      in
      let needs_register idx rd op side value =
        let value = normalize_i32 value in
        if is_compare_op op && feeds_branch idx rd then true
        else
          match op, side with
          | (Div | Mod), `Left -> true
          (* Keep an immediate divisor visible to codegen: powers of two use
             shifts and all other constants use a magic multiply-high
             sequence.  Turning it into a vreg here would force a hardware
             div/rem in the hot loop. *)
          | (Div | Mod), `Right -> false
          | Mul, _ -> not (cheap_multiply_constant value)
          | Add, _ -> not (fits_i12 value)
          | Sub, `Left -> true
          | Sub, `Right ->
            value = Int32.to_int Int32.min_int || not (fits_i12 (-value))
          | (Eq | Neq), _ -> value <> 0
          | (Lt | Gt | Le | Ge), _ -> not (fits_i12 value)
          | (And | Or), _ -> true
      in
      (* Process outer loops first: a constant used by a nested loop can then
         be materialized once for the whole surrounding loop nest. *)
      let loops =
        List.sort (fun (header1, exit1) (header2, exit2) ->
          compare (exit2 - header2) (exit1 - header1)
        ) loops
      in
      List.iter (fun (header_idx, exit_idx) ->
        let counts = Hashtbl.create 16 in
        let note value =
          let value = normalize_i32 value in
          let old =
            match Hashtbl.find_opt counts value with Some c -> c | None -> 0
          in
          Hashtbl.replace counts value (old + 1)
        in
        for idx = header_idx + 1 to exit_idx - 1 do
          match arr.(idx) with
          | Binop (rd, op, VImm value, right) ->
            if needs_register idx rd op `Left value then note value;
            (match right with
             | VImm value when needs_register idx rd op `Right value -> note value
             | _ -> ())
          | Binop (rd, op, _, VImm value) ->
            if needs_register idx rd op `Right value then note value
          | _ -> ()
        done;
        let selected =
          Hashtbl.to_seq counts
          |> List.of_seq
          |> List.sort (fun (value1, count1) (value2, count2) ->
               let by_count = compare count2 count1 in
               if by_count <> 0 then by_count else compare value1 value2)
          |> take 4
        in
        let registers = Hashtbl.create (List.length selected) in
        List.iter (fun (value, _) ->
          let reg = !next_vreg in
          incr next_vreg;
          Hashtbl.add registers value reg;
          before.(header_idx) <-
            before.(header_idx) @ [Li (reg, value)]
        ) selected;
        let rewrite_operand idx rd op side = function
          | VImm value when needs_register idx rd op side value ->
            (match Hashtbl.find_opt registers (normalize_i32 value) with
             | Some reg -> VReg reg
             | None -> VImm value)
          | operand -> operand
        in
        for idx = header_idx + 1 to exit_idx - 1 do
          arr.(idx) <-
            match arr.(idx) with
            | Binop (rd, op, left, right) ->
              Binop (rd, op,
                rewrite_operand idx rd op `Left left,
                rewrite_operand idx rd op `Right right)
            | instr -> instr
        done
      ) loops;
      let result = ref [] in
      let append instrs =
        List.iter (fun instr -> result := instr :: !result) instrs
      in
      for idx = 0 to n - 1 do
        append before.(idx);
        result := arr.(idx) :: !result
      done;
      { f with fir_body = List.rev !result }
    end

(* Rotate simple structured while loops so the normal backedge performs the
   next condition test directly.  This preserves an initial zero-iteration
   check while replacing [conditional branch + unconditional jump] with one
   conditional branch per completed iteration. *)
let rotate_simple_while_loops (f : func_ir) : func_ir =
  let arr = Array.of_list f.fir_body in
  let n = Array.length arr in
  if n = 0 then f
  else
    let _, loops = find_while_loops arr in
    if loops = [] then f
    else begin
      let next_vreg = ref (find_max_vreg f.fir_body + 1) in
      let after = Array.make n [] in
      let replacement = Array.make n None in
      let clone_condition instrs condition body_uses =
        let renames = Hashtbl.create 16 in
        let rename_reg reg =
          match Hashtbl.find_opt renames reg with
          | Some renamed -> renamed
          | None -> reg
        in
        let rename_value = function
          | VImm _ as value -> value
          | VReg reg -> VReg (rename_reg reg)
        in
        let fresh_result old =
          if IntSet.mem old body_uses then begin
            Hashtbl.replace renames old old;
            old
          end else begin
            let fresh = !next_vreg in
            incr next_vreg;
            Hashtbl.add renames old fresh;
            fresh
          end
        in
        let clone = function
          | Binop (rd, op, left, right) ->
            let left = rename_value left in
            let right = rename_value right in
            let fresh = fresh_result rd in
            (Binop (fresh, op, left, right), rd, fresh)
          | Unop (rd, op, value) ->
            let value = rename_value value in
            let fresh = fresh_result rd in
            (Unop (fresh, op, value), rd, fresh)
          | Li (rd, value) ->
            let fresh = fresh_result rd in
            (Li (fresh, value), rd, fresh)
          | Mov (rd, value) ->
            let value = rename_value value in
            let fresh = fresh_result rd in
            (Mov (fresh, value), rd, fresh)
          | Lw (rd, base, offset) ->
            let base = rename_reg base in
            let fresh = fresh_result rd in
            (Lw (fresh, base, offset), rd, fresh)
          | La (rd, name) ->
            let fresh = fresh_result rd in
            (La (fresh, name), rd, fresh)
          | Call (rd, name, args) ->
            let args = List.map rename_value args in
            let fresh = fresh_result rd in
            (Call (fresh, name, args), rd, fresh)
          | _ -> assert false
        in
        let cloned =
          List.fold_left (fun result instr ->
            let cloned, _, _ = clone instr in
            result @ [cloned]
          ) [] instrs
        in
        (cloned, rename_value condition)
      in
      List.iter (fun (header_idx, exit_idx) ->
        let header_label =
          match arr.(header_idx) with
          | Label label -> Some label
          | _ -> None
        in
        let condition_end = ref None in
        let cursor = ref (header_idx + 1) in
        while !cursor < exit_idx && !condition_end = None do
          (match arr.(!cursor) with
           | Bz (condition, exit_label) ->
             (match arr.(exit_idx) with
              | Label actual_exit when actual_exit = exit_label ->
                condition_end := Some (!cursor, condition)
              | _ -> ())
           | _ -> ());
          incr cursor
        done;
        match header_label, !condition_end with
        | Some header, Some (branch_idx, condition)
          when exit_idx > 0 ->
          let condition_instrs =
            let length = branch_idx - header_idx - 1 in
            if length <= 0 then []
            else
              Array.to_list
                (Array.sub arr (header_idx + 1) length)
          in
          let control_free =
            List.for_all (function
              | Binop _ | Unop _ | Li _ | Mov _ | Lw _ | La _ | Call _ ->
                true
              | Sw _ | Ret _ | Jmp _ | Bz _ | Bnz _ | Label _ ->
                false
            ) condition_instrs
          in
          (match arr.(exit_idx - 1) with
           | Jmp target when target = header && control_free ->
             let body_label =
               Printf.sprintf ".rot_body_%s_%d" f.fir_name header_idx
             in
             let body_uses = ref IntSet.empty in
             for idx = branch_idx + 1 to exit_idx - 2 do
               List.iter (fun reg ->
                 if reg <> 0 then body_uses := IntSet.add reg !body_uses
               ) (src_vregs arr.(idx))
             done;
             let cloned, next_condition =
               clone_condition condition_instrs condition !body_uses
             in
             after.(branch_idx) <- [Label body_label];
             replacement.(exit_idx - 1) <-
               Some (cloned @ [Bnz (next_condition, body_label)])
           | _ -> ())
        | _ -> ()
      ) loops;
      let result = ref [] in
      let append instrs =
        List.iter (fun instr -> result := instr :: !result) instrs
      in
      for idx = 0 to n - 1 do
        (match replacement.(idx) with
         | Some instrs -> append instrs
         | None -> result := arr.(idx) :: !result);
        append after.(idx)
      done;
      { f with fir_body = List.rev !result }
    end

(* After rotation the hot comparison lives on the backedge, while the older
   structured-loop constant pass has already run.  Materialize immediate
   branch operands in the unique fall-through preheader so RV32 does not need
   to execute [li] on every iteration.  The definition is placed before the
   header label: entry executes it once and backedges jump over it. *)
let materialize_backedge_branch_constants (f : func_ir) : func_ir =
  let cfg = build_cfg f.fir_body in
  let block_count = Array.length cfg.cfg_blocks in
  let instruction_count = Array.length cfg.cfg_instrs in
  if block_count = 0 || instruction_count = 0 then f
  else begin
    let rewritten = Array.copy cfg.cfg_instrs in
    let before = Array.make instruction_count [] in
    let next_vreg = ref (find_max_vreg f.fir_body + 1) in
    let is_compare = function
      | Eq | Neq | Lt | Gt | Le | Ge -> true
      | Add | Sub | Mul | Div | Mod | And | Or -> false
    in
    let feeds_branch idx rd =
      idx + 1 < instruction_count &&
      match rewritten.(idx + 1) with
      | Bz (VReg reg, _) | Bnz (VReg reg, _) -> reg = rd
      | _ -> false
    in
    let headers = ref IntSet.empty in
    Array.iter (fun block ->
      List.iter (fun successor ->
        if successor <= block.cb_id then
          headers := IntSet.add successor !headers
      ) block.cb_succs
    ) cfg.cfg_blocks;
    (* Inner headers have larger block ids.  Rewriting them first also keeps
       an outer loop from redundantly materializing the same inner bound. *)
    IntSet.elements !headers
    |> List.rev
    |> List.iter (fun header_id ->
      let latches =
        Array.fold_left (fun found block ->
          if block.cb_id >= header_id &&
             List.mem header_id block.cb_succs then
            block.cb_id :: found
          else found
        ) [] cfg.cfg_blocks
      in
      match latches with
      | [] -> ()
      | _ ->
        let last_id = List.fold_left max header_id latches in
        let outside_predecessors =
          List.filter (fun predecessor ->
            predecessor < header_id || predecessor > last_id
          ) cfg.cfg_blocks.(header_id).cb_preds
        in
        (match outside_predecessors with
         | [preheader_id] when preheader_id + 1 = header_id ->
           let preheader = cfg.cfg_blocks.(preheader_id) in
           let falls_through =
             match rewritten.(preheader.cb_end) with
             | Jmp _ | Ret _ -> false
             | _ -> true
           in
           if falls_through then begin
             let counts = Hashtbl.create 8 in
             let note value =
               let value = normalize_i32 value in
               if value <> 0 then begin
                 let count =
                   match Hashtbl.find_opt counts value with
                   | Some old -> old
                   | None -> 0
                 in
                 Hashtbl.replace counts value (count + 1)
               end
             in
             let first = cfg.cfg_blocks.(header_id).cb_start in
             let last = cfg.cfg_blocks.(last_id).cb_end in
             for idx = first to last do
               match rewritten.(idx) with
               | Binop (rd, op, VImm value, right)
                 when is_compare op && feeds_branch idx rd ->
                 note value;
                 (match right with VImm value -> note value | _ -> ())
               | Binop (rd, op, _, VImm value)
                 when is_compare op && feeds_branch idx rd ->
                 note value
               | _ -> ()
             done;
             let selected =
               Hashtbl.to_seq counts
               |> List.of_seq
               |> List.sort (fun (value1, count1) (value2, count2) ->
                    let by_count = compare count2 count1 in
                    if by_count <> 0 then by_count else compare value1 value2)
               |> take 2
             in
             let registers = Hashtbl.create (List.length selected) in
             List.iter (fun (value, _) ->
               let reg = !next_vreg in
               incr next_vreg;
               Hashtbl.add registers value reg;
               before.(first) <- before.(first) @ [Li (reg, value)]
             ) selected;
             let rewrite_operand = function
               | VImm value as operand ->
                 (match Hashtbl.find_opt registers (normalize_i32 value) with
                  | Some reg -> VReg reg
                  | None -> operand)
               | operand -> operand
             in
             for idx = first to last do
               rewritten.(idx) <-
                 match rewritten.(idx) with
                 | Binop (rd, op, left, right)
                   when is_compare op && feeds_branch idx rd ->
                   Binop (rd, op, rewrite_operand left,
                     rewrite_operand right)
                 | instr -> instr
             done
           end
         | _ -> ())
    );
    let result = ref [] in
    for idx = 0 to instruction_count - 1 do
      List.iter (fun instr -> result := instr :: !result) before.(idx);
      result := rewritten.(idx) :: !result
    done;
    { f with fir_body = List.rev !result }
  end

(* Hoist total, side-effect-free computations from structured loops.  Virtual
   registers are immutable before loop-slot caching, so a unique definition
   outside the loop (or another invariant definition) is a stable operand. *)
let loop_invariant_code_motion (f : func_ir) : func_ir =
  let arr = Array.of_list f.fir_body in
  let n = Array.length arr in
  if n = 0 then f
  else
    let _, loops = find_while_loops arr in
    if loops = [] then f
    else begin
      let definitions = Hashtbl.create 64 in
      Array.iteri (fun idx instr ->
        match def_vreg instr with
        | Some reg ->
          let old =
            match Hashtbl.find_opt definitions reg with
            | Some indices -> indices
            | None -> []
          in
          Hashtbl.replace definitions reg (idx :: old)
        | None -> ()
      ) arr;
      let unique_definition reg =
        match Hashtbl.find_opt definitions reg with
        | Some [idx] -> Some idx
        | _ -> None
      in
      let hoist_target = Array.make n None in
      let loops =
        List.sort (fun (header1, exit1) (header2, exit2) ->
          let span1 = exit1 - header1 in
          let span2 = exit2 - header2 in
          compare span2 span1
        ) loops
      in
      List.iter (fun (header_idx, exit_idx) ->
        let written_slots = ref IntSet.empty in
        for idx = header_idx + 1 to exit_idx - 1 do
          match arr.(idx) with
          | Sw (0, offset, _) ->
            written_slots := IntSet.add offset !written_slots
          | _ -> ()
        done;
        let invariant = ref IntSet.empty in
        let value_is_invariant = function
          | VImm _ | VReg 0 -> true
          | VReg reg ->
            (match unique_definition reg with
             | None -> not (Hashtbl.mem definitions reg)
             | Some def_idx ->
               def_idx < header_idx ||
               IntSet.mem def_idx !invariant ||
               (match hoist_target.(def_idx) with
                | Some target when target <= header_idx -> true
                | _ -> false))
        in
        let candidate idx =
          let has_unique_result rd =
            unique_definition rd = Some idx
          in
          match arr.(idx) with
          | Li (rd, _) | La (rd, _) ->
            has_unique_result rd
          | Mov (rd, value) | Unop (rd, _, value) ->
            has_unique_result rd && value_is_invariant value
          | Binop (rd, ((Add | Sub | Mul | Eq | Neq | Lt | Gt | Le | Ge) as _op),
                   left, right) ->
            has_unique_result rd &&
            value_is_invariant left && value_is_invariant right
          | Lw (rd, 0, offset) ->
            has_unique_result rd &&
            not (IntSet.mem offset !written_slots)
          | _ -> false
        in
        let changed = ref true in
        while !changed do
          changed := false;
          for idx = header_idx + 1 to exit_idx - 1 do
            if not (IntSet.mem idx !invariant) && candidate idx then begin
              invariant := IntSet.add idx !invariant;
              changed := true
            end
          done
        done;
        IntSet.iter (fun idx ->
          match hoist_target.(idx) with
          | None -> hoist_target.(idx) <- Some header_idx
          | Some old_target when header_idx < old_target ->
            hoist_target.(idx) <- Some header_idx
          | Some _ -> ()
        ) !invariant
      ) loops;
      let before = Array.make n [] in
      let removed = Array.make n false in
      for idx = 0 to n - 1 do
        match hoist_target.(idx) with
        | Some header_idx when header_idx <> idx ->
          before.(header_idx) <- before.(header_idx) @ [arr.(idx)];
          removed.(idx) <- true
        | _ -> ()
      done;
      let result = ref [] in
      let append instrs =
        List.iter (fun instr -> result := instr :: !result) instrs
      in
      for idx = 0 to n - 1 do
        append before.(idx);
        if not removed.(idx) then
          result := arr.(idx) :: !result
      done;
      { f with fir_body = List.rev !result }
    end

(* Unroll a counted loop only when its exact trip count is proven.

   The old optimizer guessed loop counts from unrelated [li] instructions.
   Here we require a canonical [i < constant] condition, a constant reaching
   store before the header, one [i = i + 1] update, and a body without control
   flow or calls.  If the exact trip count is divisible by four (or two), the
   body can be repeated with no remainder loop and no speculative iteration.
   This is the small ToyC counterpart of LLVM's ScalarEvolution-assisted
   LoopUnroll legality check. *)
let unroll_proven_counted_loops (f : func_ir) : func_ir =
  let arr = Array.of_list f.fir_body in
  let n = Array.length arr in
  if n = 0 then f
  else
    let _, loops = find_while_loops arr in
    let next_vreg = ref (find_max_vreg f.fir_body + 1) in
    let replacement = Array.make n None in
    let removed = Array.make n false in
    let find_definition first last reg =
      let found = ref None in
      for idx = first to last do
        if def_vreg arr.(idx) = Some reg then found := Some arr.(idx)
      done;
      !found
    in
    let reaching_initial header_idx offset =
      let rec scan idx =
        if idx < 0 then None
        else
          match arr.(idx) with
          | Sw (0, actual, VImm value) when actual = offset ->
            Some (normalize_i32 value)
          | Sw (0, actual, _) when actual = offset -> None
          | Label _ | Jmp _ | Bz _ | Bnz _ | Ret _ | Call _ -> None
          | _ -> scan (idx - 1)
      in
      scan (header_idx - 1)
    in
    let clone_body body seeds tracked_result =
      let renames = Hashtbl.create 32 in
      List.iter (fun (old_reg, new_reg) ->
        Hashtbl.replace renames old_reg new_reg
      ) seeds;
      let map_reg reg =
        match Hashtbl.find_opt renames reg with
        | Some mapped -> mapped
        | None -> reg
      in
      let map_value = function
        | VImm _ as value -> value
        | VReg reg -> VReg (map_reg reg)
      in
      let fresh old =
        let reg = !next_vreg in
        incr next_vreg;
        Hashtbl.replace renames old reg;
        reg
      in
      let cloned = List.map (function
        | Binop (rd, op, left, right) ->
          let left = map_value left in
          let right = map_value right in
          Binop (fresh rd, op, left, right)
        | Unop (rd, op, value) ->
          let value = map_value value in
          Unop (fresh rd, op, value)
        | Li (rd, value) -> Li (fresh rd, value)
        | Mov (rd, value) ->
          let value = map_value value in
          Mov (fresh rd, value)
        | Lw (rd, base, offset) ->
          let base = map_reg base in
          Lw (fresh rd, base, offset)
        | Sw (base, offset, value) ->
          Sw (map_reg base, offset, map_value value)
        | La (rd, name) -> La (fresh rd, name)
        | _ -> assert false
      ) body in
      (cloned, map_reg tracked_result)
    in
    List.iter (fun (header_idx, exit_idx) ->
      if exit_idx >= header_idx + 3 then begin
        let branch_idx = ref None in
        for idx = header_idx + 1 to exit_idx - 1 do
          match arr.(idx) with
          | Bz (_, exit_label) ->
            (match arr.(exit_idx) with
             | Label actual when actual = exit_label ->
               branch_idx := Some idx
             | _ -> ())
          | _ -> ()
        done;
        match !branch_idx, arr.(exit_idx - 1) with
        | Some cond_end, Jmp header ->
          (match arr.(header_idx) with
           | Label actual_header when actual_header = header ->
             let condition_value =
               match arr.(cond_end) with
               | Bz (VReg reg, _) -> Some reg
               | _ -> None
             in
             (match condition_value with
              | None -> ()
              | Some condition_reg ->
                (match find_definition (header_idx + 1) (cond_end - 1)
                         condition_reg with
                 | Some (Binop (_, Lt, VReg induction_reg, VImm bound)) ->
                   (match find_definition (header_idx + 1) (cond_end - 1)
                            induction_reg with
                    | Some (Lw (_, 0, offset)) ->
                      let body_first = cond_end + 1 in
                      let body_last = exit_idx - 2 in
                      let body =
                        if body_last < body_first then []
                        else Array.to_list
                          (Array.sub arr body_first
                             (body_last - body_first + 1))
                      in
                      let control_free =
                        body <> [] &&
                        List.length body <= 24 &&
                        List.for_all (function
                          | Binop _ | Unop _ | Li _ | Mov _ | Lw _ | Sw _
                          | La _ -> true
                          | Call _ | Ret _ | Jmp _ | Bz _ | Bnz _ | Label _ ->
                            false
                        ) body
                      in
                      let induction_stores =
                        List.filter_map (function
                          | Sw (0, actual, value) when actual = offset ->
                            Some value
                          | _ -> None
                        ) body
                      in
                      let canonical_update =
                        match induction_stores with
                        | [VReg update_reg] ->
                          (match find_definition body_first body_last update_reg with
                           | Some (Binop (_, Add, VReg old_reg, VImm 1))
                           | Some (Binop (_, Add, VImm 1, VReg old_reg)) ->
                             if old_reg = induction_reg ||
                                (match find_definition body_first body_last old_reg with
                                 | Some (Lw (_, 0, actual)) -> actual = offset
                                 | _ -> false)
                             then Some update_reg else None
                           | _ -> None)
                        | _ -> None
                      in
                      (match control_free, canonical_update,
                             reaching_initial header_idx offset with
                       | true, Some update_reg, Some initial ->
                         let trip =
                           Int64.sub (Int64.of_int (normalize_i32 bound))
                             (Int64.of_int initial)
                         in
                         let full_unroll =
                              Int64.compare trip 0L > 0 &&
                              Int64.compare trip 16L <= 0 &&
                              Int64.to_int trip * List.length body <= 192
                         in
                         if full_unroll then begin
                              let copies = ref body in
                              let previous_update = ref update_reg in
                              for _ = 2 to Int64.to_int trip do
                                let cloned, cloned_update =
                                  clone_body body
                                    [induction_reg, !previous_update] update_reg
                                in
                                copies := !copies @ cloned;
                                previous_update := cloned_update
                              done;
                              (* Retain the header label and the first
                                 condition's value-producing prefix.  The
                                 now-unused comparison is removed by DCE, and
                                 keeping the induction load makes body values
                                 that reuse the condition register available
                                 to the first straight-line copy. *)
                              let condition_prefix =
                                Array.to_list
                                  (Array.sub arr header_idx
                                     (cond_end - header_idx))
                              in
                              replacement.(header_idx) <-
                                Some (condition_prefix @ !copies);
                              for idx = header_idx + 1 to exit_idx - 1 do
                                removed.(idx) <- true
                              done
                            end else begin
                              let factor =
                                if Int64.compare trip 0L > 0 &&
                                   Int64.rem trip 4L = 0L then 4
                                else if Int64.compare trip 0L > 0 &&
                                        Int64.rem trip 2L = 0L then 2
                                else 1
                              in
                              if factor > 1 then begin
                                let copies = ref [] in
                                let previous_update = ref update_reg in
                                for _ = 2 to factor do
                                  let cloned, cloned_update =
                                    clone_body body
                                      [induction_reg, !previous_update]
                                      update_reg
                                  in
                                  copies := !copies @ cloned;
                                  previous_update := cloned_update
                                done;
                                replacement.(exit_idx - 1) <-
                                  Some (!copies @ [Jmp header])
                              end
                            end
                       | _ -> ())
                    | _ -> ())
                 | _ -> ()))
           | _ -> ())
        | _ -> ()
      end
    ) loops;
    let result = ref [] in
    for idx = 0 to n - 1 do
      match replacement.(idx) with
      | Some instrs ->
        List.iter (fun instr -> result := instr :: !result) instrs
      | None when not removed.(idx) -> result := arr.(idx) :: !result
      | None -> ()
    done;
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
    let label_pos, loops = find_while_loops arr in
    let is_inline_return label =
      starts_with ".inl_" label && ends_with "_end" label
    in
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
          if not (target_is_local label || is_inline_return label) then
            local := false
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
        let contains_call = ref false in
        for idx = header_idx + 1 to exit_idx - 1 do
          match arr.(idx) with
          | Call _ -> contains_call := true
          | _ -> ()
        done;
        let cache_limit =
          if !contains_call then 10
          else if f.fir_params = [] then 22
          else 12
        in
        let selected_slots =
          Hashtbl.to_seq access_counts
          |> List.of_seq
          |> List.filter (fun (_, (reads, _)) -> reads > 0)
          |> List.sort (fun (off1, (_, total1)) (off2, (_, total2)) ->
               let by_count = compare total2 total1 in
               if by_count <> 0 then by_count else compare off1 off2)
          |> take cache_limit
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

(* Promote every non-escaping source local from its stack slot to a mutable
   virtual register.

   LLVM's mem2reg constructs SSA values and inserts phi nodes at control-flow
   joins.  This IR deliberately permits a virtual register to have multiple
   definitions, so one mutable virtual register per source slot is the direct
   equivalent: the CFG itself selects the reaching definition.  The register
   allocator already computes liveness over the CFG and supports the mutable
   cache registers introduced by the older loop-only promotion.

   ToyC has neither pointers nor address-of, hence an [sp + offset] source
   slot cannot escape or alias another function.  Calls therefore need no
   flush/reload sequence; a promoted value that is live across a call is
   constrained to a callee-saved register (or spilled) by reg_alloc.ml.
   Actual spilling is left to the graph colorer, which has better loop-depth
   and interference information than a fixed "cache at most N slots" rule. *)
let promote_local_slots (f : func_ir) : func_ir =
  let offsets =
    List.fold_left (fun slots -> function
      | Lw (_, 0, offset) | Sw (0, offset, _) ->
        IntSet.add offset slots
      | _ -> slots
    ) IntSet.empty f.fir_body
  in
  if IntSet.is_empty offsets then f
  else
    let next_vreg = ref (find_max_vreg f.fir_body + 1) in
    let slot_registers = Hashtbl.create (IntSet.cardinal offsets) in
    IntSet.iter (fun offset ->
      Hashtbl.add slot_registers offset !next_vreg;
      incr next_vreg
    ) offsets;
    let promoted =
      List.map (function
        | Lw (rd, 0, offset) ->
          Mov (rd, VReg (Hashtbl.find slot_registers offset))
        | Sw (0, offset, value) ->
          Mov (Hashtbl.find slot_registers offset, value)
        | instr -> instr
      ) f.fir_body
    in
    { f with fir_body = promoted }

(* --- Driver for the local passes --- *)

let optimize_func_body (body : instr list) : instr list =
  let rec loop iter body =
    if iter >= max_iterations then body
    else
      let body' = body
        |> const_fold
        |> alg_simplify
        |> copy_prop
        |> combine_constant_chains
        |> strength_reduce
        |> combine_div_rem
        |> global_dead_store_elim
        |> dead_code_elim
        |> peephole
        |> remove_dead_after_jmp
      in
      if body' = body then body' else loop (iter + 1) body'
  in
  loop 0 body

(* --- Global value numbering / available-expression CSE --- *)

type expr_key =
  | KBinop of binop * value * value
  | KUnop  of uop   * value
  | KLi    of int
  | KLa    of string
  | KLw    of int             (* stack slot offset, Lw(0, off) only *)

module ExprMap = Map.Make(struct
  type t = expr_key
  let compare = Stdlib.compare
end)

let canonical_binop_key op left right =
  let commutative =
    match op with Add | Mul | Eq | Neq -> true | _ -> false
  in
  if commutative && Stdlib.compare left right > 0 then
    KBinop (op, right, left)
  else
    KBinop (op, left, right)

let expression_of_instr = function
  | Binop (rd, op, left, right) ->
    Some (rd, canonical_binop_key op left right)
  | Unop (rd, op, value) -> Some (rd, KUnop (op, value))
  | Li (rd, value) -> Some (rd, KLi (normalize_i32 value))
  | La (rd, name) -> Some (rd, KLa name)
  | Lw (rd, 0, offset) -> Some (rd, KLw offset)
  | _ -> None

let kill_expression_result reg expressions =
  ExprMap.filter (fun _ result -> result <> reg) expressions

let transfer_expressions expressions instr =
  let expressions =
    match def_vreg instr with
    | Some reg -> kill_expression_result reg expressions
    | None -> expressions
  in
  match instr with
  | Sw (0, offset, value) ->
    let expressions =
      ExprMap.filter (fun key _ ->
        match key with KLw old_offset -> old_offset <> offset | _ -> true
      ) expressions
    in
    (match value with
     | VReg reg -> ExprMap.add (KLw offset) reg expressions
     | VImm _ -> expressions)
  | _ ->
    (match expression_of_instr instr with
     | Some (rd, key) ->
       if ExprMap.mem key expressions then expressions
       else ExprMap.add key rd expressions
     | None -> expressions)

let intersect_expressions lhs rhs =
  ExprMap.merge (fun _ left right ->
    match left, right with
    | Some reg1, Some reg2 when reg1 = reg2 -> Some reg1
    | _ -> None
  ) lhs rhs

let cse_func (f : func_ir) : func_ir =
  let cfg = build_cfg f.fir_body in
  let block_count = Array.length cfg.cfg_blocks in
  if block_count = 0 then f
  else begin
    let reachable = reachable_blocks cfg in
    let in_states = Array.make block_count None in
    let out_states = Array.make block_count None in
    let option_equal left right =
      match left, right with
      | None, None -> true
      | Some lhs, Some rhs -> ExprMap.equal ( = ) lhs rhs
      | _ -> false
    in
    let changed = ref true in
    while !changed do
      changed := false;
      for block_id = 0 to block_count - 1 do
        if reachable.(block_id) then begin
          let block = cfg.cfg_blocks.(block_id) in
          let predecessor_states =
            List.filter_map (fun predecessor -> out_states.(predecessor))
              block.cb_preds
          in
          let incoming =
            if block_id = 0 then Some ExprMap.empty
            else
              match predecessor_states with
              | [] -> None
              | first :: rest ->
                Some (List.fold_left intersect_expressions first rest)
          in
          let outgoing =
            match incoming with
            | None -> None
            | Some expressions ->
              let expressions = ref expressions in
              for idx = block.cb_start to block.cb_end do
                expressions :=
                  transfer_expressions !expressions cfg.cfg_instrs.(idx)
              done;
              Some !expressions
          in
          if not (option_equal in_states.(block_id) incoming) ||
             not (option_equal out_states.(block_id) outgoing) then begin
            in_states.(block_id) <- incoming;
            out_states.(block_id) <- outgoing;
            changed := true
          end
        end
      done
    done;
    let rewritten = Array.copy cfg.cfg_instrs in
    Array.iteri (fun block_id block ->
      match in_states.(block_id) with
      | None -> ()
      | Some incoming ->
        let expressions = ref incoming in
        for idx = block.cb_start to block.cb_end do
          let original = rewritten.(idx) in
          let replacement =
            match expression_of_instr original with
            | Some (rd, key) ->
              (match ExprMap.find_opt key !expressions with
               | Some existing when existing <> rd ->
                 Mov (rd, VReg existing)
               | _ -> original)
            | None -> original
          in
          rewritten.(idx) <- replacement;
          expressions := transfer_expressions !expressions replacement
        done
    ) cfg.cfg_blocks;
    { f with fir_body = Array.to_list rewritten }
  end

(* --- Iterative DCE wrapper using the local dead_code_elim pass --- *)

let dce (f : func_ir) : func_ir =
  let rec loop body =
    let body' = dead_code_elim body in
    if List.length body' = List.length body then body' else loop body'
  in
  { f with fir_body = loop f.fir_body }

(* Coalesce a one-use temporary into the mutable destination introduced by
   loop/parameter caching.  RV32 instructions permit rd to equal a source, so
   patterns such as [%tmp = add %cache, 1; %cache = mov %tmp] need no move. *)
let fold_defs_into_moves (instrs : instr list) : instr list =
  let use_counts = Hashtbl.create 64 in
  List.iter (fun instr ->
    List.iter (fun reg ->
      if reg <> 0 then begin
        let old =
          match Hashtbl.find_opt use_counts reg with Some n -> n | None -> 0
        in
        Hashtbl.replace use_counts reg (old + 1)
      end
    ) (src_vregs instr)
  ) instrs;
  let used_once reg =
    Hashtbl.find_opt use_counts reg = Some 1
  in
  let replace_result new_rd = function
    | Binop (_, op, left, right) -> Binop (new_rd, op, left, right)
    | Unop (_, op, value) -> Unop (new_rd, op, value)
    | Li (_, value) -> Li (new_rd, value)
    | Mov (_, value) -> Mov (new_rd, value)
    | Lw (_, base, offset) -> Lw (new_rd, base, offset)
    | La (_, name) -> La (new_rd, name)
    | Call (_, name, args) -> Call (new_rd, name, args)
    | _ -> assert false
  in
  let rec scan acc = function
    | defining :: Mov (destination, VReg source) :: rest
      when def_vreg defining = Some source && used_once source ->
      scan (replace_result destination defining :: acc) rest
    | instr :: rest -> scan (instr :: acc) rest
    | [] -> List.rev acc
  in
  scan [] instrs

(* --- Combined optimize_func: run CSE -> local passes -> iterative DCE until convergence --- *)

let optimize_func (f : func_ir) : func_ir =
  let rec loop iter f =
    if iter >= max_iterations then f
    else
    let f1 = global_const_prop f in
    let f2 = global_copy_prop f1 |> cse_func in
    let f3 = { f2 with fir_body = optimize_func_body f2.fir_body } in
    let f4 =
      { f3 with fir_body = remove_unreachable_blocks f3.fir_body }
      |> dce
    in
    if f4.fir_body = f.fir_body then f4 else loop (iter + 1) f4
  in
  let optimized =
    f
    |> tail_rec_elim
    |> loop 0
    |> loop_invariant_code_motion
    |> loop 0
    |> unroll_proven_counted_loops
    |> loop 0
    |> materialize_loop_constants
    |> rotate_simple_while_loops
    |> materialize_backedge_branch_constants
    |> promote_local_slots
  in
  { optimized with
    fir_body =
      optimized.fir_body
      |> const_fold
      |> alg_simplify
      |> fold_defs_into_moves
      |> copy_prop
      |> strength_reduce
      |> dead_code_elim
      |> peephole
      |> remove_dead_after_jmp
      |> remove_unused_labels }

(* Inline small leaf functions.

   This follows the same broad policy as LLVM's bottom-up inliner: first make
   leaf calls disappear, then repeat so callers which became leaves can also
   be considered.  ToyC has no pointers, so an inlined callee can use a
   private slice of the caller's frame without introducing aliasing.  All
   labels and virtual registers are renamed, and every return branches to a
   call-site-specific continuation label. *)
let inline_small_leaf_functions (m : module_ir) : module_ir =
  let templates = Hashtbl.create (List.length m.mir_functions) in
  let is_inline_candidate f =
    f.fir_name <> "main" &&
    (* A larger threshold than the original straight-line-only inliner is
       profitable for ToyC: removing a helper call also exposes its local
       slots, constants and loops to the caller's whole-function passes. *)
    List.length f.fir_body <= 220 &&
    not (List.exists (function Call _ -> true | _ -> false) f.fir_body)
  in
  List.iter (fun f ->
    if is_inline_candidate f then
      Hashtbl.add templates f.fir_name f
  ) m.mir_functions;
  let inline_in_function caller =
    let next_vreg = ref (find_max_vreg caller.fir_body + 1) in
    (* Bottom-up rounds revisit the same caller.  Start after its existing
       label count so newly generated call-site labels cannot collide with
       labels produced by an earlier inlining round. *)
    let next_site =
      ref (List.fold_left (fun count -> function
        | Label _ -> count + 1
        | _ -> count
      ) 0 caller.fir_body)
    in
    let inline_area_size = ref 0 in
    (* Keep code growth bounded for pathological sources with hundreds of
       distinct cold call sites.  Calls in ordinary ToyC programs are far
       below this budget. *)
    let growth_budget = ref 2400 in
    let inline_call callee args call_result =
      let site = !next_site in
      incr next_site;
      inline_area_size := max !inline_area_size callee.fir_stack_sz;
      let registers = Hashtbl.create 64 in
      List.iteri (fun index argument ->
        Hashtbl.add registers (index + 1) argument
      ) args;
      let map_register reg =
        if reg = 0 then VReg 0
        else
          match Hashtbl.find_opt registers reg with
          | Some value -> value
          | None ->
            let fresh = !next_vreg in
            incr next_vreg;
            let value = VReg fresh in
            Hashtbl.add registers reg value;
            value
      in
      let mapped_value = function
        | VImm _ as value -> value
        | VReg reg -> map_register reg
      in
      let mapped_result reg =
        match map_register reg with
        | VReg mapped -> mapped
        | VImm _ ->
          (* Parameter virtual registers are never definitions in generated
             IR, so this case can only indicate malformed input. *)
          assert false
      in
      let labels = Hashtbl.create 16 in
      let fresh_label label =
        if is_while_end label then
          Printf.sprintf ".while_end_inl_%s_%d_%s"
            caller.fir_name site label
        else if is_while_header label then
          Printf.sprintf ".while_inl_%s_%d_%s"
            caller.fir_name site label
        else
          Printf.sprintf ".inl_%s_%d_%s" caller.fir_name site label
      in
      List.iter (function
        | Label label ->
          Hashtbl.replace labels label (fresh_label label)
        | _ -> ()
      ) callee.fir_body;
      let mapped_label label =
        match Hashtbl.find_opt labels label with
        | Some mapped -> mapped
        | None ->
          (* Every branch target in a well-formed function is represented by
             a label in that function. *)
          fresh_label label
      in
      let frame_base = caller.fir_stack_sz in
      let mapped_offset base offset =
        if base = 0 then frame_base + offset else offset
      in
      let end_label =
        Printf.sprintf ".inl_%s_%d_end" caller.fir_name site
      in
      let emitted = List.concat_map (function
        | Binop (rd, op, left, right) ->
          [Binop (mapped_result rd, op,
             mapped_value left, mapped_value right)]
        | Unop (rd, op, value) ->
          [Unop (mapped_result rd, op, mapped_value value)]
        | Li (rd, value) ->
          [Li (mapped_result rd, value)]
        | Mov (rd, value) ->
          [Mov (mapped_result rd, mapped_value value)]
        | Lw (rd, base, offset) ->
          let mapped_base =
            match map_register base with
            | VReg reg -> reg
            | VImm _ -> assert false
          in
          [Lw (mapped_result rd, mapped_base,
             mapped_offset base offset)]
        | Sw (base, offset, value) ->
          let mapped_base =
            match map_register base with
            | VReg reg -> reg
            | VImm _ -> assert false
          in
          [Sw (mapped_base, mapped_offset base offset,
             mapped_value value)]
        | La (rd, name) ->
          [La (mapped_result rd, name)]
        | Jmp label ->
          [Jmp (mapped_label label)]
        | Bz (value, label) ->
          [Bz (mapped_value value, mapped_label label)]
        | Bnz (value, label) ->
          [Bnz (mapped_value value, mapped_label label)]
        | Label label ->
          [Label (mapped_label label)]
        | Ret (Some value) ->
          [Mov (call_result, mapped_value value); Jmp end_label]
        | Ret None ->
          [Jmp end_label]
        | Call _ ->
          (* Candidates are leaves. *)
          assert false
      ) callee.fir_body in
      emitted @ [Label end_label]
    in
    let rewritten_rev =
      List.fold_left (fun result instr ->
        match instr with
        | Call (rd, name, args)
          when name <> caller.fir_name && Hashtbl.mem templates name ->
          let callee = Hashtbl.find templates name in
          let cost = List.length callee.fir_body in
          if List.length args = List.length callee.fir_params &&
             cost <= !growth_budget then begin
            growth_budget := !growth_budget - cost;
            List.rev_append (inline_call callee args rd) result
          end else
            instr :: result
        | _ -> instr :: result
      ) [] caller.fir_body
    in
    { caller with
      fir_stack_sz = caller.fir_stack_sz + !inline_area_size;
      fir_body = List.rev rewritten_rev }
  in
  { m with mir_functions = List.map inline_in_function m.mir_functions }

(* Recover the symbolic global referenced by address virtual registers.  IR
   generation emits [la] immediately before a global access, while CSE may
   later replace another [la] with a copy of an existing address. *)
let global_address_map (body : instr list) =
  let addresses = Hashtbl.create 32 in
  List.iter (function
    | La (rd, name) -> Hashtbl.replace addresses rd name
    | _ -> ()
  ) body;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (function
      | Mov (rd, VReg source) ->
        (match Hashtbl.find_opt addresses source with
         | Some name when Hashtbl.find_opt addresses rd <> Some name ->
           Hashtbl.replace addresses rd name;
           changed := true
         | _ -> ())
      | _ -> ()
    ) body
  done;
  addresses

(* LLVM's GlobalOpt can turn an internal global into a constant when the
   whole module proves that it is never modified.  Every ToyC compilation
   unit is closed and the language has no pointers, so a store through an
   unknown non-stack base is the only conservative escape case. *)
let propagate_readonly_globals (m : module_ir) : module_ir =
  let initial_values =
    List.fold_left (fun values (name, value) ->
      StringMap.add name (normalize_i32 value) values
    ) StringMap.empty m.mir_globals
  in
  if StringMap.is_empty initial_values then m
  else
    let written = ref StringMap.empty in
    let unknown_store = ref false in
    List.iter (fun f ->
      let addresses = global_address_map f.fir_body in
      List.iter (function
        | Sw (0, _, _) -> ()
        | Sw (base, 0, _) ->
          (match Hashtbl.find_opt addresses base with
           | Some name -> written := StringMap.add name () !written
           | None -> unknown_store := true)
        | Sw _ -> unknown_store := true
        | _ -> ()
      ) f.fir_body
    ) m.mir_functions;
    if !unknown_store then m
    else
      let rewrite_function f =
        let addresses = global_address_map f.fir_body in
        let body =
          List.map (function
            | Lw (rd, base, 0) ->
              (match Hashtbl.find_opt addresses base with
               | Some name when not (StringMap.mem name !written) ->
                 (match StringMap.find_opt name initial_values with
                  | Some value -> Li (rd, value)
                  | None -> Lw (rd, base, 0))
               | _ -> Lw (rd, base, 0))
            | instr -> instr
          ) f.fir_body
        in
        { f with fir_body = body }
      in
      { m with mir_functions = List.map rewrite_function m.mir_functions }

(* Promote repeatedly accessed globals inside call-free functions.  Unlike a
   local slot, a mutable global is observable by its caller, so non-main
   functions write dirty caches back on every return.  A call-free function
   cannot have its cached value invalidated while it runs. *)
let promote_hot_leaf_globals (m : module_ir) : module_ir =
  if m.mir_globals = [] then m
  else
    let rewrite_function f =
      if List.exists (function Call _ -> true | _ -> false) f.fir_body then f
      else
        let body_array = Array.of_list f.fir_body in
        let addresses = global_address_map f.fir_body in
        let cfg = build_cfg f.fir_body in
        let loop_ranges =
          Array.fold_left (fun ranges block ->
            List.fold_left (fun ranges successor ->
              if successor <= block.cb_id then
                (cfg.cfg_blocks.(successor).cb_start, block.cb_end) :: ranges
              else ranges
            ) ranges block.cb_succs
          ) [] cfg.cfg_blocks
        in
        let in_loop idx =
          List.exists (fun (first, last) -> idx >= first && idx <= last)
            loop_ranges
        in
        let accesses = Hashtbl.create 16 in
        let note name idx is_write =
          let count, hot, written =
            match Hashtbl.find_opt accesses name with
            | Some info -> info
            | None -> (0, false, false)
          in
          Hashtbl.replace accesses name
            (count + 1, hot || in_loop idx, written || is_write)
        in
        Array.iteri (fun idx -> function
          | Lw (_, base, 0) ->
            Option.iter (fun name -> note name idx false)
              (Hashtbl.find_opt addresses base)
          | Sw (base, 0, _) when base <> 0 ->
            Option.iter (fun name -> note name idx true)
              (Hashtbl.find_opt addresses base)
          | _ -> ()
        ) body_array;
        let selected =
          Hashtbl.to_seq accesses
          |> List.of_seq
          |> List.filter (fun (_, (count, hot, _)) -> hot || count >= 3)
          |> List.sort (fun (left, _) (right, _) -> compare left right)
        in
        if selected = [] then f
        else
          let next_vreg = ref (find_max_vreg f.fir_body + 1) in
          let caches = Hashtbl.create (List.length selected) in
          let preheader = ref [] in
          List.iter (fun (name, _) ->
            let address = !next_vreg in
            let cache = address + 1 in
            next_vreg := cache + 1;
            Hashtbl.add caches name cache;
            preheader := !preheader @ [La (address, name); Lw (cache, address, 0)]
          ) selected;
          let rewritten =
            List.map (function
              | Lw (rd, base, 0) ->
                (match Hashtbl.find_opt addresses base with
                 | Some name when Hashtbl.mem caches name ->
                   Mov (rd, VReg (Hashtbl.find caches name))
                 | _ -> Lw (rd, base, 0))
              | Sw (base, 0, value) when base <> 0 ->
                (match Hashtbl.find_opt addresses base with
                 | Some name when Hashtbl.mem caches name ->
                   Mov (Hashtbl.find caches name, value)
                 | _ -> Sw (base, 0, value))
              | instr -> instr
            ) f.fir_body
          in
          let dirty_names =
            List.filter_map (fun (name, (_, _, written)) ->
              if written then Some name else None
            ) selected
          in
          let flushes () =
            List.concat_map (fun name ->
              let address = !next_vreg in
              incr next_vreg;
              [La (address, name);
               Sw (address, 0, VReg (Hashtbl.find caches name))]
            ) dirty_names
          in
          let rewritten =
            if f.fir_name = "main" || dirty_names = [] then rewritten
            else
              List.concat_map (function
                | Ret _ as ret -> flushes () @ [ret]
                | instr -> [instr]
              ) rewritten
          in
          { f with fir_body = !preheader @ rewritten }
    in
    { m with mir_functions = List.map rewrite_function m.mir_functions }

(* Global-cache promotion runs after the structural loop passes.  Re-running
   the complete optimizer here would let CFG constant propagation turn a
   deliberately hoisted large loop constant back into an immediate in the
   rotated latch.  Use a local fixed-point cleanup instead. *)
let cleanup_promoted_function (f : func_ir) : func_ir =
  let f = global_copy_prop f in
  let body =
    f.fir_body
    |> optimize_func_body
    |> fold_defs_into_moves
    |> const_fold
    |> copy_prop
    |> dead_code_elim
    |> peephole
    |> remove_dead_after_jmp
    |> remove_unused_labels
  in
  { f with fir_body = body }

let optimize_module (m : module_ir) : module_ir =
  let rec inline_bottom_up rounds current =
    if rounds = 0 then current
    else
      let next = inline_small_leaf_functions current in
      if next = current then current
      else inline_bottom_up (rounds - 1) next
  in
  let inlined =
    m
    |> propagate_readonly_globals
    |> inline_bottom_up 6
    |> propagate_readonly_globals
  in
  let optimized =
    { inlined with
      mir_functions = List.map optimize_func inlined.mir_functions }
  in
  let promoted = promote_hot_leaf_globals optimized in
  { promoted with
    mir_functions =
      List.map cleanup_promoted_function promoted.mir_functions }
