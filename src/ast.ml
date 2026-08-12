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

(* ToyC has exactly one integer type: a signed 32-bit value.  Keeping compile-
   time evaluation in this domain is important because OCaml [int] is wider
   on the compiler host. *)
let normalize_i32 n =
  Int32.to_int (Int32.of_int n)

let eval_i32_binop op lhs rhs =
  let lhs = Int32.of_int lhs in
  let rhs = Int32.of_int rhs in
  let bool b = if b then 1 else 0 in
  match op with
  | Add -> Int32.to_int (Int32.add lhs rhs)
  | Sub -> Int32.to_int (Int32.sub lhs rhs)
  | Mul -> Int32.to_int (Int32.mul lhs rhs)
  | Div -> Int32.to_int (Int32.div lhs rhs)
  | Mod -> Int32.to_int (Int32.rem lhs rhs)
  | And -> bool (lhs <> Int32.zero && rhs <> Int32.zero)
  | Or  -> bool (lhs <> Int32.zero || rhs <> Int32.zero)
  | Eq  -> bool (lhs = rhs)
  | Neq -> bool (lhs <> rhs)
  | Lt  -> bool (Int32.compare lhs rhs < 0)
  | Gt  -> bool (Int32.compare lhs rhs > 0)
  | Le  -> bool (Int32.compare lhs rhs <= 0)
  | Ge  -> bool (Int32.compare lhs rhs >= 0)

let eval_i32_uop op value =
  let value = Int32.of_int value in
  match op with
  | Neg -> Int32.to_int (Int32.neg value)
  | Pos -> Int32.to_int value
  | Not -> if value = Int32.zero then 1 else 0

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
