open Ast
open Ir

(* ===================================================================
   Dead Code Elimination (DCE)
   ===================================================================
   删除定义了某虚拟寄存器但该寄存器从未被任何指令读取的纯计算指令。
   有副作用的指令（Call / Sw / Ret / Jmp / Bz / Bnz / Label）始终保留。
   迭代直到不动点：一轮删除后可能暴露出新的死代码。
   =================================================================== *)

let has_side_effect = function
  | Call _ | Sw _ | Ret _ | Jmp _ | Bz _ | Bnz _ | Label _ -> true
  | _ -> false

let collect_used (instrs : instr list) : (int, unit) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  let mark = function
    | VReg r when r <> 0 -> Hashtbl.replace tbl r ()
    | _ -> ()
  in
  List.iter (fun instr ->
    match instr with
    | Binop (_, _, v1, v2)  -> mark v1; mark v2
    | Unop  (_, _, v)
    | Mov   (_, v)
    | Bz    (v, _)
    | Bnz   (v, _)          -> mark v
    | Lw    (_, base, _)    -> if base <> 0 then Hashtbl.replace tbl base ()
    | Sw    (base, _, v)    ->
      if base <> 0 then Hashtbl.replace tbl base ();
      mark v
    | Call  (_, _, args)    -> List.iter mark args
    | Ret   (Some v)        -> mark v
    | _                     -> ()
  ) instrs;
  tbl

(* def_opt: 返回指令定义的虚拟寄存器（若有），否则 None *)
let def_opt = function
  | Binop (rd, _, _, _) | Unop (rd, _, _) | Li (rd, _) | Mov (rd, _)
  | Lw    (rd, _, _)    | La  (rd, _)     | Call (rd, _, _) ->
    if rd = 0 then None else Some rd
  | _ -> None

let dce_pass (instrs : instr list) : instr list =
  let used = collect_used instrs in
  List.filter (fun instr ->
    has_side_effect instr ||
    match def_opt instr with
    | None   -> true
    | Some r -> Hashtbl.mem used r
  ) instrs

let dce (f : func_ir) : func_ir =
  let rec loop body =
    let body' = dce_pass body in
    if List.length body' = List.length body then body' else loop body'
  in
  { f with fir_body = loop f.fir_body }

(* ===================================================================
   Common Subexpression Elimination (CSE)  —— 基本块级
   ===================================================================
   在每个基本块内（Label 处重置），记录已计算的表达式。
   若同一表达式再次出现，替换为 Mov(rd, VReg prev)，后续由 DCE 消除
   不再需要的原始计算或无用的 Mov。

   安全性：
   - ToyC 无指针，局部栈槽不会被被调用函数修改，故 Call 不会使
     KLw 失效。
   - Sw(0, off, _) 写栈槽 off，使对应 KLw off 缓存失效。
   - 算术 / Li / La 是纯计算，永不失效（除非跨 Label 重置）。
   =================================================================== *)

type expr_key =
  | KBinop of binop * value * value
  | KUnop  of uop   * value
  | KLi    of int
  | KLa    of string
  | KLw    of int             (* 栈槽偏移，仅 Lw(0, off) *)

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
      | Label _ ->
        (* 基本块边界：重置所有可用表达式（保守但正确） *)
        Hashtbl.reset tbl; instr
      | _ -> instr
    ) f.fir_body
  in
  { f with fir_body = new_body }

(* ===================================================================
   Combined optimization pipeline
   =================================================================== *)

let optimize_func (f : func_ir) : func_ir =
  (* CSE 先产生 Mov，DCE 随后清除死指令；迭代至不动点 *)
  let rec loop f =
    let f1 = cse_func f in
    let f2 = dce f1 in
    if List.length f2.fir_body = List.length f.fir_body then f2 else loop f2
  in
  loop f

let optimize_module (m : module_ir) : module_ir =
  { m with mir_functions = List.map optimize_func m.mir_functions }
