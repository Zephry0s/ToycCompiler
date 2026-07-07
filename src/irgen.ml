open Ast
open Ir
open Semant

type ctx = {
  mutable next_reg : int;
  mutable next_lbl : int;
  mutable instrs  : instr list;
  symtab          : symbol StringMap.t;
  var_offs        : int StringMap.t;
  const_vals      : int StringMap.t;
  ret_type        : type_kind;
}

let sp = 0

let new_reg ctx =
  let r = ctx.next_reg in
  ctx.next_reg <- r + 1;
  r

let new_label ctx prefix =
  let n = ctx.next_lbl in
  ctx.next_lbl <- n + 1;
  Printf.sprintf ".%s%d" prefix n

let emit ctx i =
  ctx.instrs <- i :: ctx.instrs

let rec eval_const (global_syms : symbol StringMap.t)
    (local_consts : int StringMap.t) (e : exp) : int =
  match e with
  | Num n -> n
  | Id name ->
    (match StringMap.find_opt name local_consts with
     | Some v -> v
     | None ->
       (match StringMap.find_opt name global_syms with
        | Some (SymConst v) -> v
        | _ -> failwith ("not a compile-time constant: " ^ name)))
  | Binary (l, op, r) ->
    let vl = eval_const global_syms local_consts l in
    let vr = eval_const global_syms local_consts r in
    (match op with
     | Add -> vl + vr  | Sub -> vl - vr  | Mul -> vl * vr
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
    let v = eval_const global_syms local_consts e in
    (match op with Neg -> -v | Pos -> v | Not -> if v = 0 then 1 else 0)
  | Call _ -> failwith "function call in const expression"

let frame_info (global_syms : symbol StringMap.t) (params : param list)
    (body : stmt) : int StringMap.t * int StringMap.t * int =
  let const_vals = ref StringMap.empty in
  let var_offs = ref StringMap.empty in
  let next_off = ref 4 in
  List.iter (fun p ->
    var_offs := StringMap.add p.p_name !next_off !var_offs;
    next_off := !next_off + 4
  ) params;
  let rec walk s = match s with
    | Block stmts -> List.iter walk stmts
    | If (_, th, el) -> walk th; Option.iter walk el
    | While (_, body) -> walk body
    | Decl (ConstDecl (name, init)) ->
      let v = eval_const global_syms !const_vals init in
      const_vals := StringMap.add name v !const_vals
    | Decl (VarDecl (name, _)) ->
      var_offs := StringMap.add name !next_off !var_offs;
      next_off := !next_off + 4
    | _ -> ()
  in
  walk body;
  let total = !next_off in
  let aligned = (total + 15) / 16 * 16 in
  (!var_offs, !const_vals, aligned)

let rec gen_expr (ctx : ctx) (e : exp) : vreg =
  match e with
  | Num n ->
    let r = new_reg ctx in
    emit ctx (Li (r, n));
    r
  | Id name ->
    (match StringMap.find_opt name ctx.const_vals with
     | Some v ->
       let r = new_reg ctx in
       emit ctx (Li (r, v));
       r
     | None ->
       (match StringMap.find_opt name ctx.var_offs with
        | Some off ->
          let r = new_reg ctx in
          emit ctx (Lw (r, sp, off));
          r
        | None ->
          (match StringMap.find_opt name ctx.symtab with
           | Some (SymConst v) ->
             let r = new_reg ctx in
             emit ctx (Li (r, v));
             r
           | Some SymVar ->
             let addr_r = new_reg ctx in
             let r = new_reg ctx in
             emit ctx (La (addr_r, name));
             emit ctx (Lw (r, addr_r, 0));
             r
           | _ -> failwith ("undefined variable '" ^ name ^ "'"))))
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
  let false_l = new_label ctx "land_false" in
  let end_l = new_label ctx "land_end" in
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
  let true_l = new_label ctx "lor_true" in
  let end_l = new_label ctx "lor_end" in
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
    List.iter (gen_stmt ctx brk_lbl cnt_lbl) stmts
  | Empty -> ()
  | Expr e ->
    ignore (gen_expr ctx e)
  | Assign (name, e) ->
    let r = gen_expr ctx e in
    (match StringMap.find_opt name ctx.var_offs with
     | Some off ->
       emit ctx (Sw (sp, off, VReg r))
     | None ->
       (match StringMap.find_opt name ctx.symtab with
        | Some SymVar ->
          let addr_r = new_reg ctx in
          emit ctx (La (addr_r, name));
          emit ctx (Sw (addr_r, 0, VReg r))
        | _ -> failwith ("cannot assign to '" ^ name ^ "'")))
  | If (cond, th, el) ->
    let r = gen_expr ctx cond in
    let else_l = new_label ctx "if_else" in
    let end_l = new_label ctx "if_end" in
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
    let begin_l = new_label ctx "while" in
    let end_l = new_label ctx "while_end" in
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
    let r = gen_expr ctx init in
    let off =
      match StringMap.find_opt name ctx.var_offs with
      | Some o -> o
      | None -> failwith ("no offset for local var '" ^ name ^ "'")
    in
    emit ctx (Sw (sp, off, VReg r))

let gen_func (global_syms : symbol StringMap.t) (f : func_def) : func_ir =
  let var_offs, const_vals, stack_sz =
    frame_info global_syms f.params f.body in
  let next_reg = ref (1 + List.length f.params) in
  let next_lbl = ref 0 in
  let instrs = ref [] in
  let param_list = List.mapi (fun i p ->
    (p.p_name, 4 + 4 * i)) f.params
  in
  let local_list =
    StringMap.fold (fun name off acc -> (name, off) :: acc) var_offs []
    |> List.filter (fun (name, _) ->
         not (List.exists (fun (pn, _) -> pn = name) param_list))
    |> List.sort (fun (_, a) (_, b) -> compare a b)
  in
  List.iteri (fun i p ->
    instrs := Sw (sp, 4 + 4 * i, VReg (1 + i)) :: !instrs
  ) f.params;
  let ctx = {
    next_reg = !next_reg;
    next_lbl = !next_lbl;
    instrs  = !instrs;
    symtab  = global_syms;
    var_offs;
    const_vals;
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
  let functions = ref [] in
  List.iter (fun top ->
    match top with
    | TopDecl (VarDecl (name, init)) ->
      (match StringMap.find_opt name global_syms with
       | Some (SymConst _) -> ()
       | Some SymVar ->
         let v =
           try eval_const global_syms StringMap.empty init
           with Failure _ -> 0
         in
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
