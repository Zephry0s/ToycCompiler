open Ast

let string_of_binop = function
  | Add -> "+"  | Sub -> "-"  | Mul -> "*"  | Div -> "/"  | Mod -> "%"
  | And -> "&&" | Or  -> "||"
  | Eq  -> "==" | Neq -> "!=" | Lt  -> "<"  | Gt  -> ">"  | Le -> "<=" | Ge -> ">="

let string_of_uop = function
  | Neg -> "-"  | Pos -> "+"  | Not -> "!"

let indent n = String.make (n * 2) ' '

let rec print_exp n = function
  | Binary (l, op, r) ->
      Printf.printf "%sBinary(%s)\n" (indent n) (string_of_binop op);
      print_exp (n+1) l;
      print_exp (n+1) r
  | Unary (op, e) ->
      Printf.printf "%sUnary(%s)\n" (indent n) (string_of_uop op);
      print_exp (n+1) e
  | Id s ->
      Printf.printf "%sId(%s)\n" (indent n) s
  | Num i ->
      Printf.printf "%sNum(%d)\n" (indent n) i
  | Call (name, args) ->
      Printf.printf "%sCall(%s)\n" (indent n) name;
      List.iter (print_exp (n+1)) args

let rec print_stmt n = function
  | Block stmts ->
      Printf.printf "%sBlock\n" (indent n);
      List.iter (print_stmt (n+1)) stmts
  | Empty ->
      Printf.printf "%sEmpty\n" (indent n)
  | Expr e ->
      Printf.printf "%sExprStmt\n" (indent n);
      print_exp (n+1) e
  | Assign (name, e) ->
      Printf.printf "%sAssign(%s)\n" (indent n) name;
      print_exp (n+1) e
  | If (cond, then_s, else_s) ->
      Printf.printf "%sIf\n" (indent n);
      Printf.printf "%sCondition:\n" (indent (n+1));
      print_exp (n+2) cond;
      Printf.printf "%sThen:\n" (indent (n+1));
      print_stmt (n+2) then_s;
      (match else_s with
       | Some s ->
           Printf.printf "%sElse:\n" (indent (n+1));
           print_stmt (n+2) s
       | None -> ())
  | While (cond, body) ->
      Printf.printf "%sWhile\n" (indent n);
      Printf.printf "%sCondition:\n" (indent (n+1));
      print_exp (n+2) cond;
      Printf.printf "%sBody:\n" (indent (n+1));
      print_stmt (n+2) body
  | Break ->
      Printf.printf "%sBreak\n" (indent n)
  | Continue ->
      Printf.printf "%sContinue\n" (indent n)
  | Return e_opt ->
      Printf.printf "%sReturn\n" (indent n);
      (match e_opt with Some e -> print_exp (n+1) e | None -> ())
  | Decl d ->
      print_decl n d

and print_decl n = function
  | ConstDecl (name, init) ->
      Printf.printf "%sConstDecl(%s)\n" (indent n) name;
      Printf.printf "%sInit:\n" (indent (n+1));
      print_exp (n+2) init
  | VarDecl (name, init) ->
      Printf.printf "%sVarDecl(%s)\n" (indent n) name;
      Printf.printf "%sInit:\n" (indent (n+1));
      print_exp (n+2) init

let print_param n p =
  Printf.printf "%sParam(%s : int)\n" (indent n) p.p_name

let string_of_type = function Int -> "int" | Void -> "void"

let print_func n f =
  Printf.printf "%sFuncDef(%s : %s)\n" (indent n) f.name (string_of_type f.ret_type);
  if f.params <> [] then begin
    Printf.printf "%sParams:\n" (indent (n+1));
    List.iter (print_param (n+2)) f.params
  end;
  Printf.printf "%sBody:\n" (indent (n+1));
  print_stmt (n+2) f.body

let print_top n = function
  | TopDecl d -> print_decl n d
  | TopFunc f -> print_func n f

let print_comp_unit tops =
  Printf.printf "CompUnit\n";
  List.iter (print_top 1) tops
