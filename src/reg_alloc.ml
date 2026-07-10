open Ir

module ISet = Set.Make(struct type t = int let compare = compare end)
module IMap = Map.Make(struct type t = int let compare = compare end)
module SMap = Map.Make(String)

let phys_regs = [|"t0"; "t1"; "t2"; "t3"; "t4";
                  "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
                  "s8"; "s9"; "s10"; "s11"|]

let num_regs = Array.length phys_regs
let spill_temp1 = "t5"
let spill_temp2 = "t6"

let is_callee_saved r = String.length r > 0 && r.[0] = 's'

type alloc =
  | Reg of string
  | Spill of int

type func_alloc = {
  fa_reg_map     : (int, alloc) Hashtbl.t;
  fa_callee_used : string list;
  fa_spill_sz    : int;
}

(* ---------- use/def per instruction ---------- *)

let use_set = function
  | Binop (_, _, v1, v2) ->
    let s = match v1 with VReg r -> if r = 0 then ISet.empty else ISet.singleton r | _ -> ISet.empty in
    (match v2 with VReg r -> if r = 0 then ISet.empty else ISet.add r s | _ -> s)
  | Unop (_, _, v) | Mov (_, v) ->
    (match v with VReg r -> if r = 0 then ISet.empty else ISet.singleton r | _ -> ISet.empty)
  | Lw (_, base, _) ->
    if base = 0 then ISet.empty else ISet.singleton base
  | Sw (base, _, v) ->
    let s = match v with VReg r -> if r = 0 then ISet.empty else ISet.singleton r | _ -> ISet.empty in
    if base = 0 then s else ISet.add base s
  | Call (_, _, args) ->
    List.fold_left (fun s v ->
      match v with VReg r -> if r = 0 then s else ISet.add r s | _ -> s) ISet.empty args
  | Ret (Some v) ->
    (match v with VReg r -> if r = 0 then ISet.empty else ISet.singleton r | _ -> ISet.empty)
  | Bz (v, _) | Bnz (v, _) ->
    (match v with VReg r -> if r = 0 then ISet.empty else ISet.singleton r | _ -> ISet.empty)
  | Li _ | La _ | Jmp _ | Label _ | Ret None -> ISet.empty

let def_opt = function
  | Binop (rd, _, _, _) | Unop (rd, _, _) | Li (rd, _) | Mov (rd, _)
  | Lw (rd, _, _) | La (rd, _) | Call (rd, _, _) ->
    if rd = 0 then None else Some rd
  | _ -> None

(* ---------- basic block ---------- *)

type bb = {
  bb_id    : int;
  bb_label : string;
  bb_start : int;
  bb_end   : int;
  mutable bb_succs : int list;
}

let build_blocks (instrs : instr list) : instr array * bb array =
  let n = List.length instrs in
  let instr_arr = Array.of_list instrs in

  let starts = Array.make n false in
  if n > 0 then starts.(0) <- true;
  for i = 0 to n - 1 do
    match instr_arr.(i) with
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
      let label = match instr_arr.(start) with
        | Label s -> s
        | _ -> Printf.sprintf ".Lentry%d" !block_id
      in
      let j = ref (start + 1) in
      while !j < n && not starts.(!j) do
        incr j
      done;
      let last_idx = !j - 1 in
      let bb = {
        bb_id = !block_id; bb_label = label;
        bb_start = start; bb_end = last_idx;
        bb_succs = []
      } in
      blocks := bb :: !blocks;
      label_map := SMap.add label !block_id !label_map;
      incr block_id;
      i := !j
    end else
      incr i
  done;

  let bb_arr = Array.of_list (List.rev !blocks) in

  for bid = 0 to Array.length bb_arr - 1 do
    let bb = bb_arr.(bid) in
    let last = instr_arr.(bb.bb_end) in
    let succs = match last with
      | Jmp lbl ->
        (match SMap.find_opt lbl !label_map with Some id -> [id] | None -> [])
      | Bz (_, lbl) | Bnz (_, lbl) ->
        let tgt = (match SMap.find_opt lbl !label_map with Some id -> [id] | None -> []) in
        let fall = if bid + 1 < Array.length bb_arr then [bid + 1] else [] in
        tgt @ fall
      | Ret _ -> []
      | _ ->
        if bid + 1 < Array.length bb_arr then [bid + 1] else []
    in
    bb_arr.(bid).bb_succs <- succs
  done;

  (instr_arr, bb_arr)

(* ---------- block-level use/def ---------- *)

let compute_use_def (instr_arr : instr array) (bb_arr : bb array) =
  let n = Array.length bb_arr in
  let use_arr = Array.make n ISet.empty in
  let def_arr = Array.make n ISet.empty in
  for bid = 0 to n - 1 do
    let bb = bb_arr.(bid) in
    let def_sofar = ref ISet.empty in
    for idx = bb.bb_start to bb.bb_end do
      let inst = instr_arr.(idx) in
      let u = ISet.diff (use_set inst) !def_sofar in
      use_arr.(bid) <- ISet.union use_arr.(bid) u;
      (match def_opt inst with
       | Some r -> def_arr.(bid) <- ISet.add r def_arr.(bid);
         def_sofar := ISet.add r !def_sofar
       | None -> ())
    done
  done;
  (use_arr, def_arr)

(* ---------- iterative liveness ---------- *)

let compute_liveness (bb_arr : bb array) (use_arr : ISet.t array) (def_arr : ISet.t array) =
  let n = Array.length bb_arr in
  let live_in = Array.make n ISet.empty in
  let live_out = Array.make n ISet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for bid = n - 1 downto 0 do
      let new_out =
        List.fold_left (fun s succ -> ISet.union s live_in.(succ))
          ISet.empty bb_arr.(bid).bb_succs in
      let new_in = ISet.union use_arr.(bid) (ISet.diff new_out def_arr.(bid)) in
      if not (ISet.equal live_out.(bid) new_out) || not (ISet.equal live_in.(bid) new_in) then begin
        live_out.(bid) <- new_out;
        live_in.(bid) <- new_in;
        changed := true
      end
    done;
    for bid = 0 to n - 1 do
      let new_out =
        List.fold_left (fun s succ -> ISet.union s live_in.(succ))
          ISet.empty bb_arr.(bid).bb_succs in
      let new_in = ISet.union use_arr.(bid) (ISet.diff new_out def_arr.(bid)) in
      if not (ISet.equal live_out.(bid) new_out) || not (ISet.equal live_in.(bid) new_in) then begin
        live_out.(bid) <- new_out;
        live_in.(bid) <- new_in;
        changed := true
      end
    done
  done;
  (live_in, live_out)

(* ---------- intervals ---------- *)

type interval = {
  i_vreg  : int;
  i_start : int;
  i_end   : int;
}

let compute_intervals (instr_arr : instr array) (bb_arr : bb array)
    (live_in : ISet.t array) (live_out : ISet.t array) =
  let first_def = ref IMap.empty in
  let last_use = ref IMap.empty in
  let call_positions = ref ISet.empty in

  for bid = 0 to Array.length bb_arr - 1 do
    let bb = bb_arr.(bid) in
    let live = ref live_out.(bid) in

    let rec walk idx =
      if idx >= bb.bb_start then begin
        let inst = instr_arr.(idx) in

        (match inst with
         | Call _ -> call_positions := ISet.add idx !call_positions
         | _ -> ());

        let live_set = match def_opt inst with
          | Some r -> ISet.remove r !live
          | None -> !live
        in
        live := ISet.union live_set (use_set inst);

        ISet.iter (fun r ->
          if r <> 0 then
            last_use := IMap.update r (fun old ->
              match old with Some v -> Some (max v idx) | None -> Some idx) !last_use
        ) !live;

        (match def_opt inst with
         | Some r when r <> 0 ->
           first_def := IMap.update r (fun old ->
             match old with Some v -> Some (min v idx) | None -> Some idx) !first_def
         | _ -> ());

        walk (idx - 1)
      end
    in
    walk bb.bb_end
  done;

  if Array.length bb_arr > 0 then
    ISet.iter (fun r ->
      if r <> 0 && not (IMap.mem r !first_def) then
        first_def := IMap.add r 0 !first_def
    ) live_in.(0);

  (!first_def, !last_use, !call_positions)

(* ---------- linear scan ---------- *)

let linear_scan (first_def : int IMap.t) (last_use : int IMap.t) (call_positions : ISet.t) : func_alloc =
  let intervals = ref [] in
  IMap.iter (fun vreg start ->
    let last = match IMap.find_opt vreg last_use with
      | Some l -> l | None -> start
    in
    if start <= last then
      intervals := { i_vreg = vreg; i_start = start; i_end = last } :: !intervals
  ) first_def;

  let intervals = List.sort (fun a b -> compare a.i_start b.i_start) !intervals in

  let spans_call iv =
    try
      let _ = ISet.find_first (fun pos -> pos >= iv.i_start && pos <= iv.i_end) call_positions in
      true
    with Not_found -> false
  in

  let is_caller_saved r =
    String.length r > 0 && r.[0] = 't'
  in

  let reg_map = Hashtbl.create 64 in
  let callee_used = ref [] in

  let active = Array.make num_regs (None : (int * int) option) in
  let next_spill = ref 0 in

  let find_free ?(avoid_caller_saved = false) () =
    let rec loop i =
      if i >= num_regs then None
      else if active.(i) = None then
        if avoid_caller_saved && is_caller_saved phys_regs.(i) then loop (i + 1)
        else Some i
      else loop (i + 1)
    in loop 0
  in

  let expire_active cur_start =
    for i = 0 to num_regs - 1 do
      match active.(i) with
      | Some (_, e) when e < cur_start -> active.(i) <- None
      | _ -> ()
    done
  in

  List.iter (fun iv ->
    expire_active iv.i_start;

    let need_callee = spans_call iv in
    let idx =
      match find_free ~avoid_caller_saved:need_callee () with
      | Some i -> Some i
      | None when need_callee ->
        find_free ()
      | None -> None
    in

    (match idx with
    | Some idx ->
      active.(idx) <- Some (iv.i_vreg, iv.i_end);
      Hashtbl.replace reg_map iv.i_vreg (Reg phys_regs.(idx));
      if is_callee_saved phys_regs.(idx) &&
         not (List.mem phys_regs.(idx) !callee_used) then
        callee_used := phys_regs.(idx) :: !callee_used
    | None ->
      let spill_idx = ref 0 in
      let max_end = ref (-1) in
      for i = 0 to num_regs - 1 do
        match active.(i) with
        | Some (_, e) when e > !max_end ->
          spill_idx := i;
          max_end := e
        | _ -> ()
      done;

      if !max_end > iv.i_end then begin
        let spilled = Option.get active.(!spill_idx) in
        let off = !next_spill in
        Hashtbl.replace reg_map (fst spilled) (Spill off);
        next_spill := !next_spill + 4;
        active.(!spill_idx) <- Some (iv.i_vreg, iv.i_end);
        Hashtbl.replace reg_map iv.i_vreg (Reg phys_regs.(!spill_idx));
        if is_callee_saved phys_regs.(!spill_idx) &&
           not (List.mem phys_regs.(!spill_idx) !callee_used) then
          callee_used := phys_regs.(!spill_idx) :: !callee_used
      end else begin
        let off = !next_spill in
        Hashtbl.replace reg_map iv.i_vreg (Spill off);
        next_spill := !next_spill + 4
      end
    )
  ) intervals;

  IMap.iter (fun vreg _ ->
    if not (Hashtbl.mem reg_map vreg) then begin
      let off = !next_spill in
      Hashtbl.replace reg_map vreg (Spill off);
      next_spill := !next_spill + 4
    end
  ) first_def;

  { fa_reg_map     = reg_map;
    fa_callee_used = !callee_used;
    fa_spill_sz    = !next_spill }

let alloc_func (f : func_ir) : func_alloc =
  let instr_arr, bb_arr = build_blocks f.fir_body in
  let use_arr, def_arr = compute_use_def instr_arr bb_arr in
  let live_in, live_out = compute_liveness bb_arr use_arr def_arr in
  let first_def, last_use, call_positions = compute_intervals instr_arr bb_arr live_in live_out in
  linear_scan first_def last_use call_positions
