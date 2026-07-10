open Ast

module StringMap = Map.Make (String)

type symbol =
  | SymVar
  | SymVarVal of int
  | SymConst of int
  | SymParam
  | SymFunc of func_info

and func_info = {
  f_ret  : type_kind;
  f_params : param list;
}

type scope_stack = symbol StringMap.t list

let enter_scope (st : scope_stack) : scope_stack =
  StringMap.empty :: st

let leave_scope (st : scope_stack) : scope_stack =
  match st with [] -> [] | _ :: rest -> rest

let add_symbol (st : scope_stack) name sym : scope_stack =
  match st with
  | [] -> [StringMap.add name sym StringMap.empty]
  | cur :: rest -> StringMap.add name sym cur :: rest

let rec lookup (st : scope_stack) name : symbol option =
  match st with
  | [] -> None
  | scope :: rest ->
    (match StringMap.find_opt name scope with
     | Some _ as result -> result
     | None -> lookup rest name)

let s2i = string_of_int

let rec try_eval_const (st : scope_stack) (e : exp) : int =
  match e with
  | Num n -> n
  | Id name ->
    (match lookup st name with
     | Some (SymConst v) | Some (SymVarVal v) -> v
     | _ -> failwith ("not a compile-time constant: " ^ name))
  | Binary (l, op, r) ->
    let vl = try_eval_const st l in
    let vr = try_eval_const st r in
    (match op with
     | Add -> vl + vr
     | Sub -> vl - vr
     | Mul -> vl * vr
     | Div -> if vr = 0 then failwith "division by zero" else vl / vr
     | Mod -> if vr = 0 then failwith "division by zero" else vl mod vr
     | And -> if vl <> 0 && vr <> 0 then 1 else 0
     | Or  -> if vl <> 0 || vr <> 0 then 1 else 0
     | Eq  -> if vl = vr  then 1 else 0
     | Neq -> if vl <> vr then 1 else 0
     | Lt  -> if vl < vr  then 1 else 0
     | Gt  -> if vl > vr  then 1 else 0
     | Le  -> if vl <= vr then 1 else 0
     | Ge  -> if vl >= vr then 1 else 0)
  | Unary (op, e) ->
    let v = try_eval_const st e in
    (match op with
     | Neg -> -v
     | Pos -> v
     | Not -> if v = 0 then 1 else 0)
  | Call _ ->
    failwith "function call not allowed in const initializer"

let rec is_const_expr (st : scope_stack) (e : exp) : bool =
  match e with
  | Num _ -> true
  | Id name ->
    (match lookup st name with
      | Some (SymConst _) -> true
     | _ -> false)
  | Binary (l, _, r) -> is_const_expr st l && is_const_expr st r
  | Unary (_, e) -> is_const_expr st e
  | Call _ -> false

let rec all_paths_return (s : stmt) : bool =
  match s with
  | Block stmts -> List.exists all_paths_return stmts
  | Return (Some _) -> true
  | Return None -> false
  | If (_, th, Some el) -> all_paths_return th && all_paths_return el
  | If _ -> false
  | While _ -> false
  | Break | Continue -> false
  | Empty | Expr _ | Assign _ | Decl _ -> false

let rec check_decl (st : scope_stack) (d : decl) : scope_stack =
  match d with
  | ConstDecl (name, init) ->
    if not (is_const_expr st init) then
      failwith ("const '" ^ name ^ "' initializer must be compile-time constant");
    let v = try_eval_const st init in
    add_symbol st name (SymConst v)
  | VarDecl (name, init) ->
    let t = check_exp st init in
    if t = Void then failwith ("variable '" ^ name ^ "' cannot be initialized with void function call");
    add_symbol st name SymVar

and check_exp (st : scope_stack) (e : exp) : type_kind =
  match e with
  | Num _ -> Int
  | Id name ->
    (match lookup st name with
     | Some (SymVar | SymVarVal _ | SymParam | SymConst _) -> Int
     | Some (SymFunc _) -> failwith ("function '" ^ name ^ "' used as value")
     | None -> failwith ("undefined identifier '" ^ name ^ "'"))
  | Unary (_, e) ->
    let t = check_exp st e in
    if t <> Int then failwith "unary operator requires int operand"
    else Int
  | Binary (l, _, r) ->
    let tl = check_exp st l in
    let tr = check_exp st r in
    if tl <> Int || tr <> Int then
      failwith "binary operator requires int operands"
    else Int
  | Call (fname, args) ->
    (match lookup st fname with
     | Some (SymFunc fi) ->
       let param_count = List.length fi.f_params in
       let arg_count = List.length args in
       if param_count <> arg_count then
         failwith ("function '" ^ fname ^ "' expects " ^ s2i param_count ^
                   " arguments, got " ^ s2i arg_count);
       List.iter (fun arg -> ignore (check_exp st arg)) args;
       fi.f_ret
     | _ -> failwith ("undefined function '" ^ fname ^ "'"))

and check_stmt (st : scope_stack) (in_loop : bool) (ret_type : type_kind)
    (s : stmt) : scope_stack =
  match s with
  | Block stmts ->
    let inner = check_stmt_seq (enter_scope st) in_loop ret_type stmts in
    leave_scope inner
  | Empty -> st
  | Expr e ->
    ignore (check_exp st e);
    st
  | Assign (name, e) ->
    let t = check_exp st e in
    if t = Void then failwith "cannot assign void expression";
    (match lookup st name with
     | Some (SymConst _) -> failwith ("cannot assign to const '" ^ name ^ "'")
     | Some (SymFunc _) -> failwith ("function '" ^ name ^ "' is not assignable")
      | Some (SymVar | SymVarVal _ | SymParam) -> st
     | None -> failwith ("undefined variable '" ^ name ^ "'"))
  | If (cond, th, el) ->
    ignore (check_cond st cond);
    ignore (check_stmt st in_loop ret_type th);
    (match el with
     | Some el_s -> ignore (check_stmt st in_loop ret_type el_s)
     | None -> ());
    st
  | While (cond, body) ->
    ignore (check_cond st cond);
    ignore (check_stmt st true ret_type body);
    st
  | Break ->
    if not in_loop then failwith "break not in loop";
    st
  | Continue ->
    if not in_loop then failwith "continue not in loop";
    st
  | Return e_opt ->
    (match ret_type, e_opt with
     | Int, None ->
       failwith "return value required in int function"
     | Int, Some e ->
       let t = check_exp st e in
       if t = Void then failwith "cannot return void expression";
       st
     | Void, Some _ ->
       failwith "void function should not return a value"
     | Void, None -> st)
  | Decl d ->
    check_decl st d

and check_cond (st : scope_stack) (e : exp) : type_kind =
  let t = check_exp st e in
  if t = Void then failwith "condition cannot be void expression";
  t

and check_stmt_seq (st : scope_stack) (in_loop : bool) (ret_type : type_kind)
    (stmts : stmt list) : scope_stack =
  List.fold_left (fun acc s -> check_stmt acc in_loop ret_type s) st stmts

let check_top_decl (st : scope_stack) (d : decl) : scope_stack =
  match d with
  | VarDecl (name, init) ->
    if not (is_const_expr st init) then
      failwith ("global variable '" ^ name ^ "' initializer must be compile-time constant");
    let v = try_eval_const st init in
    let t = check_exp st init in
    if t = Void then failwith ("variable '" ^ name ^ "' cannot be initialized with void function call");
    add_symbol st name (SymVarVal v)
  | _ -> check_decl st d

let check_func_body (global_st : scope_stack) (f : func_def) : unit =
  let func_st = enter_scope global_st in
  let func_st = List.fold_left (fun st p ->
    add_symbol st p.p_name SymParam
  ) func_st f.params in
  ignore (check_stmt func_st false f.ret_type f.body);
  if f.ret_type = Int && not (all_paths_return f.body) then
    failwith ("function '" ^ f.name ^ "' must return a value on all paths")

let check_comp_unit (cu : comp_unit) : symbol StringMap.t =
  let globals = ref StringMap.empty in
  List.iter (fun top ->
    match top with
    | TopFunc f ->
      if StringMap.mem f.name !globals then
        failwith ("duplicate function '" ^ f.name ^ "'");
      let fi = { f_ret = f.ret_type; f_params = f.params } in
      globals := StringMap.add f.name (SymFunc fi) !globals
    | TopDecl _ -> ()
  ) cu;
  (match StringMap.find_opt "main" !globals with
   | Some (SymFunc fi) ->
     if fi.f_ret <> Int then
       failwith "main function must return int";
     if fi.f_params <> [] then
       failwith "main function must have no parameters"
    | _ -> failwith "no main function defined");
  let check_top (st : scope_stack) (top : top) : scope_stack =
    match top with
    | TopDecl d ->
      check_top_decl st d
    | TopFunc f ->
      let fi = { f_ret = f.ret_type; f_params = f.params } in
      let st = add_symbol st f.name (SymFunc fi) in
      check_func_body st f;
      st
  in
  let final = List.fold_left check_top [StringMap.empty] cu in
  match final with
  | [m] -> m
  | _ -> !globals
