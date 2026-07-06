type binop =
  | Add | Sub | Mul | Div | Mod
  | And | Or
  | Eq | Neq | Lt | Gt | Le | Ge

type exp =
  | Binary of exp * binop * exp
  | Unary  of uop * exp
  | Id     of string
  | Num    of int
  | Call   of string * exp list

and uop =
  | Neg | Pos | Not

type stmt =
  | Block   of stmt list
  | Empty
  | Expr    of exp
  | Assign  of string * exp
  | If      of exp * stmt * stmt option
  | While   of exp * stmt
  | Break
  | Continue
  | Return  of exp option
  | Decl    of decl

and decl =
  | ConstDecl of string * exp
  | VarDecl   of string * exp

type type_kind =
  | Int | Void

type func_def = {
  ret_type : type_kind;
  name     : string;
  params   : param list;
  body     : stmt;
}

and param = {
  p_name : string;
}

type top =
  | TopDecl of decl
  | TopFunc of func_def

type comp_unit = top list
