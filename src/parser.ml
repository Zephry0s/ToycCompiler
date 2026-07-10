open Token
open Ast

exception Error of string

type state = {
  token : Lexing.lexbuf -> token;
  lexbuf : Lexing.lexbuf;
  mutable cur : token;
  mutable peek : token;
}

let pos_line st =
  let p = Lexing.lexeme_start_p st.lexbuf in
  p.pos_lnum

let pos_col st =
  let p = Lexing.lexeme_start_p st.lexbuf in
  p.pos_cnum - p.pos_bol + 1

let parse_error st msg : 'a =
  raise (Error (Printf.sprintf "line %d, col %d: %s" (pos_line st) (pos_col st) msg))

let next st =
  st.cur <- st.peek;
  st.peek <- st.token st.lexbuf

let init token_fun lexbuf =
  let st = { token = token_fun; lexbuf; cur = EOF; peek = EOF } in
  next st; next st;
  st

let check st t = st.cur = t

let is_id st = match st.cur with ID _ -> true | _ -> false
let is_num st = match st.cur with NUMBER _ -> true | _ -> false

let get_id st = match st.cur with ID s -> s | _ -> "?"
let get_num st = match st.cur with NUMBER n -> n | _ -> 0

let eat_id st =
  let s = get_id st in next st; s

let eat_num st =
  let n = get_num st in next st; n

let match_token st t =
  if check st t then (next st; true)
  else false

let expect st t msg =
  if check st t then next st
  else parse_error st msg

let expect_id st msg =
  if is_id st then eat_id st
  else parse_error st msg

let expect_num st msg =
  if is_num st then eat_num st
  else parse_error st msg

let rec parse_comp_unit st =
  let items = ref [] in
  while not (check st EOF) do
    let top = parse_top st in
    items := top :: !items
  done;
  List.rev !items

and parse_top st =
  if check st CONST then
    let d = parse_const_decl st in TopDecl d
  else if check st INT || check st VOID then begin
    let ret = parse_type_kind st in
    let name = expect_id st "expected identifier" in
    if check st LPAREN then
      parse_func_tail st ret name
    else if check st ASSIGN then begin
      next st;
      let init = parse_expr st in
      expect st SEMICOLON "expected ';'";
      TopDecl (VarDecl (name, init))
    end else
      parse_error st "expected '(' for function or '=' for variable declaration"
  end else
    parse_error st "expected declaration or function definition"

and parse_func_tail st ret name =
  expect st LPAREN "expected '('";
  let params = ref [] in
  if not (check st RPAREN) then begin
    params := [parse_param st];
    while match_token st COMMA do
      params := parse_param st :: !params
    done
  end;
  expect st RPAREN "expected ')'";
  let body = parse_block st in
  TopFunc { ret_type = ret; name; params = List.rev !params; body = Block body }

and parse_type_kind st =
  if match_token st INT then Int
  else if match_token st VOID then Void
  else parse_error st "expected 'int' or 'void'"

and parse_func_def st =
  let ret = parse_type_kind st in
  let name = expect_id st "expected function name" in
  expect st LPAREN "expected '('";
  let params = ref [] in
  if not (check st RPAREN) then begin
    params := [parse_param st];
    while match_token st COMMA do
      params := parse_param st :: !params
    done
  end;
  expect st RPAREN "expected ')'";
  let body = parse_block st in
  { ret_type = ret; name; params = List.rev !params; body = Block body }

and parse_param st =
  expect st INT "expected 'int' in parameter";
  let name = expect_id st "expected parameter name" in
  { p_name = name }

and parse_const_decl st =
  expect st CONST "expected 'const'";
  expect st INT "expected 'int'";
  let name = expect_id st "expected constant name" in
  expect st ASSIGN "expected '='";
  let init = parse_expr st in
  expect st SEMICOLON "expected ';'";
  ConstDecl (name, init)

and parse_var_decl st =
  expect st INT "expected 'int'";
  let name = expect_id st "expected variable name" in
  expect st ASSIGN "expected '='";
  let init = parse_expr st in
  expect st SEMICOLON "expected ';'";
  VarDecl (name, init)

and parse_decl st =
  if check st CONST then
    let d = parse_const_decl st in Decl d
  else
    let d = parse_var_decl st in Decl d

and parse_block st =
  expect st LBRACE "expected '{'";
  let stmts = ref [] in
  while not (check st RBRACE) && not (check st EOF) do
    stmts := parse_stmt st :: !stmts
  done;
  expect st RBRACE "expected '}'";
  List.rev !stmts

and parse_stmt st =
  match st.cur with
  | LBRACE ->
      let b = parse_block st in Block b
  | SEMICOLON ->
      next st; Empty
  | CONST ->
      let d = parse_const_decl st in Decl d
  | INT ->
      let d = parse_var_decl st in Decl d
  | IF ->
      next st;
      expect st LPAREN "expected '(' after 'if'";
      let cond = parse_expr st in
      expect st RPAREN "expected ')'";
      let then_s = parse_stmt st in
      let else_s = if match_token st ELSE then Some (parse_stmt st) else None in
      If (cond, then_s, else_s)
  | WHILE ->
      next st;
      expect st LPAREN "expected '(' after 'while'";
      let cond = parse_expr st in
      expect st RPAREN "expected ')'";
      let body = parse_stmt st in
      While (cond, body)
  | BREAK ->
      next st; expect st SEMICOLON "expected ';'"; Break
  | CONTINUE ->
      next st; expect st SEMICOLON "expected ';'"; Continue
  | RETURN ->
      next st;
      let val_opt =
        if check st SEMICOLON then None
        else Some (parse_expr st)
      in
      expect st SEMICOLON "expected ';'";
      Return val_opt
  | ID _ ->
      let id_name = eat_id st in
      if match_token st ASSIGN then begin
        let val_e = parse_expr st in
        expect st SEMICOLON "expected ';'";
        Assign (id_name, val_e)
      end else begin
        let e = parse_expr_from st (parse_expr_tail st (Id id_name)) in
        expect st SEMICOLON "expected ';'";
        Expr e
      end
  | LPAREN | MINUS | PLUS | BANG ->
      let e = parse_expr st in
      expect st SEMICOLON "expected ';'";
      Expr e
  | NUMBER _ ->
      let e = parse_expr st in
      expect st SEMICOLON "expected ';'";
      Expr e
  | _ ->
      parse_error st "expected statement"

and parse_expr_from st init =
  let rec loop_add acc =
    let rec loop_mul a =
      if match_token st STAR then loop_mul (Binary (a, Mul, parse_unary st))
      else if match_token st SLASH then loop_mul (Binary (a, Div, parse_unary st))
      else if match_token st PERCENT then loop_mul (Binary (a, Mod, parse_unary st))
      else a
    in
    let m = loop_mul acc in
    if match_token st PLUS then loop_add (Binary (m, Add, parse_mul st))
    else if match_token st MINUS then loop_add (Binary (m, Sub, parse_mul st))
    else m
  in
  let rec loop_rel acc =
    let a = loop_add acc in
    let op =
      if match_token st LT then Some Lt
      else if match_token st GT then Some Gt
      else if match_token st LE then Some Le
      else if match_token st GE then Some Ge
      else if match_token st EQEQ then Some Eq
      else if match_token st NEQ then Some Neq
      else None
    in
    match op with Some o -> loop_rel (Binary (a, o, parse_add st)) | None -> a
  in
  let rec loop_land acc =
    let r = loop_rel acc in
    if match_token st AMPAMP then loop_land (Binary (r, And, parse_rel st))
    else r
  in
  let rec loop_lor acc =
    let a = loop_land acc in
    if match_token st PIPEPIPE then loop_lor (Binary (a, Or, parse_land st))
    else a
  in
  loop_lor init

and parse_expr st = parse_lor st

and parse_lor st =
  let left = parse_land st in
  let rec loop acc =
    if match_token st PIPEPIPE then
      let right = parse_land st in
      loop (Binary (acc, Or, right))
    else acc
  in loop left

and parse_land st =
  let left = parse_rel st in
  let rec loop acc =
    if match_token st AMPAMP then
      let right = parse_rel st in
      loop (Binary (acc, And, right))
    else acc
  in loop left

and parse_rel st =
  let left = parse_add st in
  let rec loop acc =
    let op =
      if match_token st LT then Some Lt
      else if match_token st GT then Some Gt
      else if match_token st LE then Some Le
      else if match_token st GE then Some Ge
      else if match_token st EQEQ then Some Eq
      else if match_token st NEQ then Some Neq
      else None
    in
    match op with
    | Some o -> let right = parse_add st in loop (Binary (acc, o, right))
    | None -> acc
  in loop left

and parse_add st =
  let left = parse_mul st in
  let rec loop acc =
    if match_token st PLUS then
      let right = parse_mul st in loop (Binary (acc, Add, right))
    else if match_token st MINUS then
      let right = parse_mul st in loop (Binary (acc, Sub, right))
    else acc
  in loop left

and parse_mul st =
  let left = parse_unary st in
  let rec loop acc =
    if match_token st STAR then
      let right = parse_unary st in loop (Binary (acc, Mul, right))
    else if match_token st SLASH then
      let right = parse_unary st in loop (Binary (acc, Div, right))
    else if match_token st PERCENT then
      let right = parse_unary st in loop (Binary (acc, Mod, right))
    else acc
  in loop left

and parse_unary st =
  if match_token st MINUS then
    let e = parse_unary st in Unary (Neg, e)
  else if match_token st PLUS then
    let e = parse_unary st in Unary (Pos, e)
  else if match_token st BANG then
    let e = parse_unary st in Unary (Not, e)
  else
    parse_primary st

and parse_primary st =
  match st.cur with
  | NUMBER n ->
      next st; Num n
  | LPAREN ->
      next st;
      let e = parse_expr st in
      expect st RPAREN "expected ')'";
      e
  | ID id ->
      next st;
      parse_expr_tail st (Id id)
  | _ ->
      parse_error st "expected expression"

and parse_expr_tail st lhs =
  if match_token st LPAREN then begin
    let args = ref [] in
    if not (check st RPAREN) then begin
      args := [parse_expr st];
      while match_token st COMMA do
        args := parse_expr st :: !args
      done
    end;
    let fname = match lhs with Id s -> s | _ -> "?" in
    expect st RPAREN "expected ')'";
    Call (fname, List.rev !args)
  end else
    lhs

let comp_unit token_fun lexbuf =
  let st = init token_fun lexbuf in
  try
    let ast = parse_comp_unit st in
    if not (check st EOF) then
      parse_error st "expected end of file";
    ast
  with Error msg ->
    raise (Error msg)
