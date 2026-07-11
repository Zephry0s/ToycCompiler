open Ast
open Ir
open Semant

type ctx = {
  mutable next_reg : int;
  mutable instrs  : instr list;
  symtab          : symbol StringMap.t;
  var_by_scope    : (int StringMap.t) list;
  const_by_scope  : (int StringMap.t) list;
  scope_parent    : int list;
  mutable cur_scope : int;
  mutable next_scope : int;
  mutable hidden_local : (int * string) option;
  ret_type        : type_kind;
}

let sp = 0

let rec scope_find name scope_id maps scope_parent =
  if scope_id < 0 then None
  else
    match StringMap.find_opt name (List.nth maps scope_id) with
    | Some _ as v -> v
    | None -> scope_find name (List.nth scope_parent scope_id) maps scope_parent

let var_lookup ctx name =
  scope_find name ctx.cur_scope ctx.var_by_scope ctx.scope_parent

let const_lookup ctx name =
  scope_find name ctx.cur_scope ctx.const_by_scope ctx.scope_parent

type local_binding =
  | LocalVar of int
  | LocalConst of int

let rec local_lookup ctx name scope_id =
  if scope_id < 0 then None
  else if ctx.hidden_local = Some (scope_id, name) then
    local_lookup ctx name (List.nth ctx.scope_parent scope_id)
  else
    match StringMap.find_opt name (List.nth ctx.var_by_scope scope_id) with
    | Some off -> Some (LocalVar off)
    | None ->
      (match StringMap.find_opt name (List.nth ctx.const_by_scope scope_id) with
       | Some value -> Some (LocalConst value)
       | None -> local_lookup ctx name (List.nth ctx.scope_parent scope_id))

let new_reg ctx =
  let r = ctx.next_reg in
  ctx.next_reg <- r + 1;
  r

let global_lbl = ref 0

let new_label prefix =
  let n = !global_lbl in
  global_lbl := n + 1;
  Printf.sprintf ".%s%d" prefix n

let emit ctx i =
  ctx.instrs <- i :: ctx.instrs

let rec eval_const (global_syms : symbol StringMap.t)
    (local_consts : int StringMap.t) (global_vals : int StringMap.t) (e : exp) : int =
  match e with
  | Num n -> n
  | Id name ->
    (match StringMap.find_opt name local_consts with
     | Some v -> v
     | None ->
       (match StringMap.find_opt name global_vals with
        | Some v -> v
        | None ->
          (match StringMap.find_opt name global_syms with
           | Some (SymConst v) | Some (SymVarVal v) -> v
           | _ -> failwith ("not a compile-time constant: " ^ name))))
  | Binary (l, op, r) ->
    let vl = eval_const global_syms local_consts global_vals l in
    (match op with
     | And -> if vl = 0 then 0 else if eval_const global_syms local_consts global_vals r <> 0 then 1 else 0
     | Or  -> if vl <> 0 then 1 else if eval_const global_syms local_consts global_vals r <> 0 then 1 else 0
     | _ ->
       let vr = eval_const global_syms local_consts global_vals r in
       match op with
       | Add -> vl + vr  | Sub -> vl - vr  | Mul -> vl * vr
       | Div -> if vr = 0 then failwith "division by zero" else vl / vr
       | Mod -> if vr = 0 then failwith "division by zero" else vl mod vr
       | Eq  -> if vl = vr  then 1 else 0
       | Neq -> if vl <> vr then 1 else 0
       | Lt  -> if vl < vr  then 1 else 0
       | Gt  -> if vl > vr  then 1 else 0
       | Le  -> if vl <= vr then 1 else 0
       | Ge  -> if vl >= vr then 1 else 0
       | And | Or -> assert false)
  | Unary (op, e) ->
    let v = eval_const global_syms local_consts global_vals e in
    (match op with Neg -> -v | Pos -> v | Not -> if v = 0 then 1 else 0)
  | Call _ -> failwith "function call in const expression"

let frame_info (global_syms : symbol StringMap.t) (params : param list)
    (body : stmt) : (int StringMap.t) list * (int StringMap.t) list * int list * int =
  let var_maps = ref [StringMap.empty] in
  let const_maps = ref [StringMap.empty] in
  let scope_parent = ref [(-1)] in
  let cur_scope = ref 0 in
  let next_off = ref 4 in
  let add_entry maps_ref name value =
    let idx = !cur_scope in
    while List.length !maps_ref <= idx do
      maps_ref := !maps_ref @ [StringMap.empty]
    done;
    maps_ref := List.mapi (fun i m ->
      if i = idx then StringMap.add name value m else m
    ) !maps_ref
  in
  let add_var name =
    add_entry var_maps name !next_off;
    next_off := !next_off + 4
  and add_const name v =
    add_entry const_maps name v
  in
  let visible_consts () =
    let rec scope_chain scope_id =
      if scope_id < 0 then []
      else scope_chain (List.nth !scope_parent scope_id) @ [scope_id]
    in
    List.fold_left (fun values scope_id ->
      let values =
        StringMap.fold (fun name _ acc -> StringMap.remove name acc)
          (List.nth !var_maps scope_id) values
      in
      StringMap.fold StringMap.add (List.nth !const_maps scope_id) values
    ) StringMap.empty (scope_chain !cur_scope)
  in
  List.iter (fun p -> add_var p.p_name) params;
  let rec walk s = match s with
    | Block stmts ->
      let parent = !cur_scope in
      cur_scope := List.length !var_maps;
      while List.length !scope_parent <= !cur_scope do
        scope_parent := !scope_parent @ [(-1)]
      done;
      scope_parent := List.mapi (fun i p ->
        if i = !cur_scope then parent else p
      ) !scope_parent;
      while List.length !var_maps <= !cur_scope do
        var_maps := !var_maps @ [StringMap.empty];
        const_maps := !const_maps @ [StringMap.empty]
      done;
      List.iter walk stmts;
      cur_scope := parent
    | If (_, th, el) -> walk th; Option.iter walk el
    | While (_, body) -> walk body
    | Decl (ConstDecl (name, init)) ->
      let v = eval_const global_syms (visible_consts ()) StringMap.empty init in
      add_const name v
    | Decl (VarDecl (name, _)) ->
      add_var name
    | _ -> ()
  in
  let body_stmts = match body with
    | Block stmts -> stmts
    | _ -> [body]
  in
  List.iter walk body_stmts;
  let total = !next_off in
  let aligned = (total + 15) / 16 * 16 in
  (!var_maps, !const_maps, !scope_parent, aligned)

let rec gen_expr (ctx : ctx) (e : exp) : vreg =
  match e with
  | Num n ->
    let r = new_reg ctx in
    emit ctx (Li (r, n));
    r
  | Id name ->
    (match local_lookup ctx name ctx.cur_scope with
     | Some (LocalConst v) ->
       let r = new_reg ctx in
       emit ctx (Li (r, v));
       r
     | Some (LocalVar off) ->
       let r = new_reg ctx in
       emit ctx (Lw (r, sp, off));
       r
     | None ->
       (match StringMap.find_opt name ctx.symtab with
        | Some (SymConst v) ->
          let r = new_reg ctx in
          emit ctx (Li (r, v));
          r
        | Some SymVar | Some (SymVarVal _) ->
          let addr_r = new_reg ctx in
          let r = new_reg ctx in
          emit ctx (La (addr_r, name));
          emit ctx (Lw (r, addr_r, 0));
          r
        | _ -> failwith ("undefined variable '" ^ name ^ "'")))
  | Unary (op, e) ->
    let r = gen_expr ctx e in
    let rd = new_reg ctx in
    (match op with
     | Pos -> emit ctx (Mov (rd, VReg r))
     | Neg | Not -> emit ctx (Unop (rd, op, VReg r)));
    rd
  | Binary (l, And, r) ->
    gen_land ctx l r
  | Binary (l, Or, r) ->
    gen_lor ctx l r
  | Binary (l, op, r) ->
    let rl = gen_expr ctx l in
    let rr = gen_expr ctx r in
    let rd = new_reg ctx in
    emit ctx (Binop (rd, op, VReg rl, VReg rr));
    rd
  | Call (fname, args) ->
    let arg_regs = List.map (gen_expr ctx) args in
    let rd = new_reg ctx in
    emit ctx (Call (rd, fname, List.map (fun r -> VReg r) arg_regs));
    rd

and gen_land ctx l r =
  let rd = new_reg ctx in
  let false_l = new_label "land_false" in
  let end_l = new_label "land_end" in
  let rl = gen_expr ctx l in
  emit ctx (Bz (VReg rl, false_l));
  let rr = gen_expr ctx r in
  emit ctx (Bz (VReg rr, false_l));
  emit ctx (Li (rd, 1));
  emit ctx (Jmp end_l);
  emit ctx (Label false_l);
  emit ctx (Li (rd, 0));
  emit ctx (Label end_l);
  rd

and gen_lor ctx l r =
  let rd = new_reg ctx in
  let true_l = new_label "lor_true" in
  let end_l = new_label "lor_end" in
  let rl = gen_expr ctx l in
  emit ctx (Bnz (VReg rl, true_l));
  let rr = gen_expr ctx r in
  emit ctx (Bnz (VReg rr, true_l));
  emit ctx (Li (rd, 0));
  emit ctx (Jmp end_l);
  emit ctx (Label true_l);
  emit ctx (Li (rd, 1));
  emit ctx (Label end_l);
  rd

let rec gen_stmt (ctx : ctx) (brk_lbl : string) (cnt_lbl : string)
    (s : stmt) : unit =
  match s with
  | Block stmts ->
    let parent_scope = ctx.cur_scope in
    ctx.cur_scope <- ctx.next_scope;
    ctx.next_scope <- ctx.next_scope + 1;
    List.iter (gen_stmt ctx brk_lbl cnt_lbl) stmts;
    ctx.cur_scope <- parent_scope
  | Empty -> ()
  | Expr e ->
    ignore (gen_expr ctx e)
  | Assign (name, e) ->
    let r = gen_expr ctx e in
    (match local_lookup ctx name ctx.cur_scope with
     | Some (LocalVar off) ->
       emit ctx (Sw (sp, off, VReg r))
     | Some (LocalConst _) ->
       failwith ("cannot assign to const '" ^ name ^ "'")
     | None ->
        (match StringMap.find_opt name ctx.symtab with
         | Some SymVar | Some (SymVarVal _) ->
           let addr_r = new_reg ctx in
           emit ctx (La (addr_r, name));
           emit ctx (Sw (addr_r, 0, VReg r))
         | _ -> failwith ("cannot assign to '" ^ name ^ "'")))
  | If (cond, th, el) ->
    let r = gen_expr ctx cond in
    let else_l = new_label "if_else" in
    let end_l = new_label "if_end" in
    emit ctx (Bz (VReg r, else_l));
    gen_stmt ctx brk_lbl cnt_lbl th;
    (match el with
     | Some el_s ->
       emit ctx (Jmp end_l);
       emit ctx (Label else_l);
       gen_stmt ctx brk_lbl cnt_lbl el_s
     | None ->
       emit ctx (Label else_l));
    emit ctx (Label end_l)
  | While (cond, body) ->
    let begin_l = new_label "while" in
    let end_l = new_label "while_end" in
    emit ctx (Label begin_l);
    let r = gen_expr ctx cond in
    emit ctx (Bz (VReg r, end_l));
    gen_stmt ctx end_l begin_l body;
    emit ctx (Jmp begin_l);
    emit ctx (Label end_l)
  | Break ->
    emit ctx (Jmp brk_lbl)
  | Continue ->
    emit ctx (Jmp cnt_lbl)
  | Return e_opt ->
    (match e_opt with
     | Some e ->
       let r = gen_expr ctx e in
       emit ctx (Ret (Some (VReg r)))
     | None ->
       emit ctx (Ret None))
  | Decl (ConstDecl (_, _)) ->
    ()
  | Decl (VarDecl (name, init)) ->
    (* A declaration is not visible inside its own initializer.  This matters
       for `int x = x + 1` in a scope that shadows an outer x. *)
    let old_hidden = ctx.hidden_local in
    ctx.hidden_local <- Some (ctx.cur_scope, name);
    let r =
      try
        let value = gen_expr ctx init in
        ctx.hidden_local <- old_hidden;
        value
      with exn ->
        ctx.hidden_local <- old_hidden;
        raise exn
    in
    let off =
      match var_lookup ctx name with
      | Some o -> o
      | None -> failwith ("no offset for local var '" ^ name ^ "'")
    in
    emit ctx (Sw (sp, off, VReg r))

let gen_func (global_syms : symbol StringMap.t) (f : func_def) : func_ir =
  let var_maps, const_maps, scope_parent, stack_sz =
    frame_info global_syms f.params f.body in
  let next_reg = ref (1 + List.length f.params) in
  let instrs = ref [] in
  let param_list = List.mapi (fun i p ->
    (p.p_name, 4 + 4 * i)) f.params
  in
  let all_vars = List.fold_left (fun acc m ->
    StringMap.fold (fun name off acc2 -> (name, off) :: acc2) m acc
  ) [] var_maps in
  let param_end =
    if f.params = [] then 0 else 4 + 4 * (List.length f.params - 1) in
  let local_list =
    all_vars
    |> List.filter (fun (_, off) -> off > param_end)
    |> List.sort (fun (_, a) (_, b) -> compare a b)
  in
  List.iteri (fun i _ ->
    instrs := Sw (sp, 4 + 4 * i, VReg (1 + i)) :: !instrs
  ) f.params;
  let ctx = {
    next_reg = !next_reg;
    instrs  = !instrs;
    symtab  = global_syms;
    var_by_scope = var_maps;
    const_by_scope = const_maps;
    scope_parent;
    cur_scope = 0;
    next_scope = 1;
    hidden_local = None;
    ret_type = f.ret_type;
  } in
  (match f.body with
   | Block stmts -> List.iter (gen_stmt ctx ".ret" ".ret") stmts
   | _ -> failwith "function body must be a block");
  (match ctx.instrs with
   | (Ret _) :: _ -> ()
   | _ ->
     if f.ret_type = Void then
       emit ctx (Ret None)
     else
       emit ctx (Ret (Some (VImm 0))));
  {
    fir_name     = f.name;
    fir_params   = param_list;
    fir_locals   = local_list;
    fir_stack_sz = stack_sz;
    fir_ret_type = f.ret_type;
    fir_body     = List.rev ctx.instrs;
  }

let gen_module (global_syms : symbol StringMap.t) (cu : comp_unit) : module_ir =
  let globals = ref [] in
  let global_vals = ref StringMap.empty in
  let functions = ref [] in
  List.iter (fun top ->
    match top with
    | TopDecl (VarDecl (name, init)) ->
       (match StringMap.find_opt name global_syms with
        | Some (SymConst _) -> ()
        | Some (SymVarVal v) ->
          global_vals := StringMap.add name v !global_vals;
          globals := (name, v) :: !globals
        | Some SymVar ->
          let v =
            try eval_const global_syms StringMap.empty !global_vals init
            with Failure _ -> 0
          in
          global_vals := StringMap.add name v !global_vals;
          globals := (name, v) :: !globals
        | _ -> ())
    | TopDecl (ConstDecl _) -> ()
    | TopFunc f ->
      functions := gen_func global_syms f :: !functions
  ) cu;
  {
    mir_globals   = List.rev !globals;
    mir_functions = List.rev !functions;
  }
