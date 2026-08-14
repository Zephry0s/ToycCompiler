open Ir

module ISet = Set.Make(struct type t = int let compare = compare end)
module IMap = Map.Make(struct type t = int let compare = compare end)
module SMap = Map.Make(String)

let default_phys_regs =
  [|"t0"; "t1"; "t2"; "t3"; "t4";
    "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
    "s8"; "s9"; "s10"; "s11"|]

(* A parameterless leaf has no ABI argument values to preserve and no call
   that can clobber a-registers.  Treat a0-a7 as additional caller-saved
   registers, as LLVM/GCC do after leaf-function analysis. *)
let leaf_phys_regs =
  [|"t0"; "t1"; "t2"; "t3"; "t4";
    "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
    "s8"; "s9"; "s10"; "s11"|]

(* [main] exits with an ecall and never consumes its incoming return address,
   so [ra] is one more allocatable register when main itself is a leaf. *)
let main_leaf_phys_regs =
  Array.append leaf_phys_regs [|"ra"|]

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

let linear_scan (phys_regs : string array) (avoid_argument_regs : ISet.t)
    (call_result_regs : ISet.t) (first_def : int IMap.t)
    (last_use : int IMap.t) (call_positions : ISet.t) : func_alloc =
  let num_regs = Array.length phys_regs in
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
    (* [Set.find_first] requires a monotone predicate.  Testing both interval
       bounds with it is not monotone and can miss an earlier call when a
       function contains many call sites. *)
    try
      let next_call =
        ISet.find_first (fun pos -> pos > iv.i_start) call_positions
      in
      next_call < iv.i_end
    with Not_found -> false
  in

  let is_caller_saved r =
    String.length r > 0 && (r.[0] = 't' || r.[0] = 'a')
  in

  let reg_map = Hashtbl.create 64 in
  let callee_used = ref [] in

  let active = Array.make num_regs (None : (int * int) option) in
  let next_spill = ref 0 in

  let is_argument_register r =
    String.length r > 0 && r.[0] = 'a'
  in

  let find_free ?(callee_only = false) ?(avoid_a = false)
      ?(prefer_a0 = false) () =
    let preferred =
      if prefer_a0 && not avoid_a && not callee_only then begin
        let found = ref None in
        for i = 0 to num_regs - 1 do
          if phys_regs.(i) = "a0" && active.(i) = None then
            found := Some i
        done;
        !found
      end else None
    in
    let rec loop i =
      if i >= num_regs then None
      else if active.(i) = None then
        if (callee_only && is_caller_saved phys_regs.(i)) ||
           (avoid_a && is_argument_register phys_regs.(i))
        then loop (i + 1)
        else Some i
      else loop (i + 1)
    in
    match preferred with Some idx -> Some idx | None -> loop 0
  in

  let expire_active cur_start =
    for i = 0 to num_regs - 1 do
      match active.(i) with
      (* A definition may reuse a source register whose final use is the same
         instruction: RV32 reads both sources before writing [rd].  Modeling
         intervals as half-open at that boundary is the small linear-scan
         equivalent of LLVM's early-clobber-aware live-range coalescing. *)
      | Some (_, e) when e <= cur_start -> active.(i) <- None
      | _ -> ()
    done
  in

  List.iter (fun iv ->
    expire_active iv.i_start;

    let need_callee = spans_call iv in
    let avoid_a = ISet.mem iv.i_vreg avoid_argument_regs in
    let prefer_a0 = ISet.mem iv.i_vreg call_result_regs in
    let idx =
      find_free ~callee_only:need_callee ~avoid_a ~prefer_a0 ()
    in

    (match idx with
    | Some idx ->
      active.(idx) <- Some (iv.i_vreg, iv.i_end);
      Hashtbl.replace reg_map iv.i_vreg (Reg phys_regs.(idx));
      if is_callee_saved phys_regs.(idx) &&
         not (List.mem phys_regs.(idx) !callee_used) then
        callee_used := phys_regs.(idx) :: !callee_used
    | None ->
      let spill_idx = ref None in
      let max_end = ref (-1) in
      for i = 0 to num_regs - 1 do
        let eligible =
          (not need_callee || is_callee_saved phys_regs.(i)) &&
          (not avoid_a || not (is_argument_register phys_regs.(i)))
        in
        match eligible, active.(i) with
        | true, Some (_, e) when e > !max_end ->
          spill_idx := Some i;
          max_end := e
        | _ -> ()
      done;

      if !max_end > iv.i_end && !spill_idx <> None then begin
        let idx = Option.get !spill_idx in
        let spilled = Option.get active.(idx) in
        let off = !next_spill in
        Hashtbl.replace reg_map (fst spilled) (Spill off);
        next_spill := !next_spill + 4;
        active.(idx) <- Some (iv.i_vreg, iv.i_end);
        Hashtbl.replace reg_map iv.i_vreg (Reg phys_regs.(idx));
        if is_callee_saved phys_regs.(idx) &&
           not (List.mem phys_regs.(idx) !callee_used) then
          callee_used := phys_regs.(idx) :: !callee_used
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

(* ---------- interference-graph coloring ---------- *)

let graph_color (phys_regs : string array) (avoid_argument_regs : ISet.t)
    (call_result_regs : ISet.t) (parameter_count : int)
    (instr_arr : instr array)
    (bb_arr : bb array) (live_in : ISet.t array)
    (live_out : ISet.t array) : func_alloc =
  let num_regs = Array.length phys_regs in
  let adjacency = Hashtbl.create 128 in
  let move_partners = Hashtbl.create 64 in
  let weights = Hashtbl.create 128 in
  let across_calls = ref ISet.empty in
  let nodes = ref ISet.empty in

  let ensure_node reg =
    if reg <> 0 then begin
      nodes := ISet.add reg !nodes;
      if not (Hashtbl.mem adjacency reg) then
        Hashtbl.add adjacency reg ISet.empty
    end
  in
  let add_edge left right =
    if left <> 0 && right <> 0 && left <> right then begin
      ensure_node left;
      ensure_node right;
      Hashtbl.replace adjacency left
        (ISet.add right (Hashtbl.find adjacency left));
      Hashtbl.replace adjacency right
        (ISet.add left (Hashtbl.find adjacency right))
    end
  in
  let add_move left right =
    if left <> 0 && right <> 0 && left <> right then begin
      let add_one from_reg to_reg =
        let old =
          match Hashtbl.find_opt move_partners from_reg with
          | Some set -> set
          | None -> ISet.empty
        in
        Hashtbl.replace move_partners from_reg (ISet.add to_reg old)
      in
      add_one left right;
      add_one right left
    end
  in
  (* Incoming parameters have no defining IR instruction.  Add their
     entry-live clique explicitly; otherwise two simultaneously live
     arguments could be assigned the same physical register. *)
  if Array.length live_in > 0 then
    ISet.iter (fun left ->
      ISet.iter (fun right -> add_edge left right) live_in.(0)
    ) live_in.(0);
  let backedges =
    Array.fold_left (fun edges block ->
      List.fold_left (fun edges successor ->
        if successor <= block.bb_id then (successor, block.bb_id) :: edges
        else edges
      ) edges block.bb_succs
    ) [] bb_arr
  in
  let block_weight block_id =
    let depth =
      List.fold_left (fun depth (header, latch) ->
        if block_id >= header && block_id <= latch then depth + 1 else depth
      ) 0 backedges
    in
    if depth <= 0 then 1
    else if depth = 1 then 10
    else if depth = 2 then 100
    else 1000
  in
  let add_weight reg amount =
    if reg <> 0 then begin
      ensure_node reg;
      let old =
        match Hashtbl.find_opt weights reg with Some value -> value | None -> 0
      in
      Hashtbl.replace weights reg (old + amount)
    end
  in

  Array.iter (fun block ->
    let weight = block_weight block.bb_id in
    let live = ref live_out.(block.bb_id) in
    ISet.iter ensure_node !live;
    for idx = block.bb_end downto block.bb_start do
      let instr = instr_arr.(idx) in
      let uses = use_set instr in
      ISet.iter (fun reg -> add_weight reg weight) uses;
      (match def_opt instr with
       | Some rd ->
         add_weight rd weight;
         (* A move's source and destination may share a color: the source is
            consumed before the destination becomes live.  Excluding that
            single source from the interference edges is the standard
            move-aware construction and lets the existing preference logic
            erase loop-carried and copy-propagation moves. *)
         let interferes_with =
           match instr with
           | Mov (_, VReg source) -> ISet.remove source !live
           | _ -> !live
         in
         ISet.iter (fun live_reg -> add_edge rd live_reg) interferes_with;
         (match instr with
          | Mov (_, VReg source) -> add_move rd source
          | _ -> ())
       | None -> ());
      (match instr with
       | Call (rd, _, _) ->
         across_calls := ISet.union !across_calls (ISet.remove rd !live)
       | _ -> ());
      live :=
        ISet.union uses
          (match def_opt instr with
           | Some rd -> ISet.remove rd !live
           | None -> !live)
    done
  ) bb_arr;

  let is_argument_register reg =
    String.length reg > 0 && reg.[0] = 'a'
  in
  let allowed_colors vreg =
    let needs_callee = ISet.mem vreg !across_calls in
    let avoids_a = ISet.mem vreg avoid_argument_regs in
    let colors = ref [] in
    for color = num_regs - 1 downto 0 do
      let reg = phys_regs.(color) in
      if (not needs_callee || is_callee_saved reg) &&
         (not avoids_a || not (is_argument_register reg))
      then colors := color :: !colors
    done;
    !colors
  in
  let colors = Hashtbl.create 128 in
  (* Keep non-call-crossing incoming arguments in their ABI registers.  This
     is equivalent to precoloring LLVM's physical-register copies and removes
     both entry moves and needless callee-saved saves. *)
  for parameter = 1 to min 8 parameter_count do
    if not (ISet.mem parameter !across_calls) &&
       not (ISet.mem parameter avoid_argument_regs) then
      for color = 0 to num_regs - 1 do
        if phys_regs.(color) = "a" ^ string_of_int (parameter - 1) then
          Hashtbl.replace colors parameter color
      done
  done;
  let remaining = ref !nodes in
  let stack = ref [] in
  let remaining_degree reg =
    match Hashtbl.find_opt adjacency reg with
    | None -> 0
    | Some neighbors ->
      ISet.cardinal (ISet.inter neighbors !remaining)
  in
  while not (ISet.is_empty !remaining) do
    let low_degree =
      ISet.fold (fun reg choice ->
        let degree = remaining_degree reg in
        if degree < List.length (allowed_colors reg) then
          match choice with
          | None -> Some reg
          | Some old when degree > remaining_degree old -> Some reg
          | Some _ -> choice
        else choice
      ) !remaining None
    in
    let chosen =
      match low_degree with
      | Some reg -> reg
      | None ->
        (* Potential spill: evict the coldest value per interference edge.
           Loop-depth weighting keeps induction and reduction values in
           registers ahead of one-shot setup temporaries. *)
        ISet.fold (fun reg best ->
          let weight =
            match Hashtbl.find_opt weights reg with Some value -> value | None -> 1
          in
          let degree = max 1 (remaining_degree reg) in
          match best with
          | None -> Some (reg, weight, degree)
          | Some (_, best_weight, best_degree) as old ->
            if weight * best_degree < best_weight * degree then
              Some (reg, weight, degree)
            else old
        ) !remaining None
        |> Option.get
        |> fun (reg, _, _) -> reg
    in
    remaining := ISet.remove chosen !remaining;
    stack := chosen :: !stack
  done;

  let reg_map = Hashtbl.create 128 in
  let callee_used = ref [] in
  let next_spill = ref 0 in
  let color_available used color = not (ISet.mem color used) in
  List.iter (fun reg ->
    let used_colors =
      match Hashtbl.find_opt adjacency reg with
      | None -> ISet.empty
      | Some neighbors ->
        ISet.fold (fun neighbor used ->
          match Hashtbl.find_opt colors neighbor with
          | Some color -> ISet.add color used
          | None -> used
        ) neighbors ISet.empty
    in
    let allowed = allowed_colors reg in
    let move_preference =
      match Hashtbl.find_opt move_partners reg with
      | None -> None
      | Some partners ->
        ISet.fold (fun partner choice ->
          match choice, Hashtbl.find_opt colors partner with
          | Some _, _ -> choice
          | None, Some color
            when List.mem color allowed && color_available used_colors color ->
            Some color
          | None, _ -> None
        ) partners None
    in
    let a0_preference =
      if ISet.mem reg call_result_regs then begin
        let found = ref None in
        List.iter (fun color ->
          if phys_regs.(color) = "a0" &&
             color_available used_colors color then found := Some color
        ) allowed;
        !found
      end else None
    in
    let chosen_color =
      match Hashtbl.find_opt colors reg with
      | Some color -> Some color
      | None ->
        (match move_preference, a0_preference with
         | Some color, _ -> Some color
         | None, Some color -> Some color
         | None, None ->
           List.find_opt (color_available used_colors) allowed)
    in
    match chosen_color with
    | Some color ->
      Hashtbl.replace colors reg color;
      let physical = phys_regs.(color) in
      Hashtbl.replace reg_map reg (Reg physical);
      if is_callee_saved physical &&
         not (List.mem physical !callee_used) then
        callee_used := physical :: !callee_used
    | None ->
      Hashtbl.replace reg_map reg (Spill !next_spill);
      next_spill := !next_spill + 4
  ) !stack;
  { fa_reg_map = reg_map;
    fa_callee_used = !callee_used;
    fa_spill_sz = !next_spill }

let alloc_func (f : func_ir) : func_alloc =
  let instr_arr, bb_arr = build_blocks f.fir_body in
  let use_arr, def_arr = compute_use_def instr_arr bb_arr in
  let live_in, live_out = compute_liveness bb_arr use_arr def_arr in
  let first_def, last_use, call_positions = compute_intervals instr_arr bb_arr live_in live_out in
  (* Values used as call arguments stay out of a0-a7.  This lets codegen keep
     its simple left-to-right argument setup without a parallel-copy cycle,
     while every other non-cross-call interval can still use the expanded
     caller-saved register bank.  Incoming parameter vregs are excluded for
     the same reason. *)
  let avoid_argument_regs =
    Array.fold_left (fun set -> function
      | Call (_, _, args) ->
        List.fold_left (fun set -> function
          | VReg reg when reg <> 0 -> ISet.add reg set
          | VReg _ | VImm _ -> set
        ) set args
      | _ -> set
    ) ISet.empty instr_arr
  in
  let call_result_regs =
    Array.fold_left (fun set -> function
      | Call (rd, _, _) when rd <> 0 -> ISet.add rd set
      | _ -> set
    ) ISet.empty instr_arr
  in
  let phys_regs =
    if ISet.is_empty call_positions && f.fir_params = [] &&
       f.fir_name = "main" then main_leaf_phys_regs
    else if ISet.is_empty call_positions && f.fir_params = [] then
      leaf_phys_regs
    else default_phys_regs
  in
  ignore first_def;
  ignore last_use;
  graph_color phys_regs avoid_argument_regs call_result_regs
    (List.length f.fir_params) instr_arr bb_arr live_in live_out
