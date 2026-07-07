open Ast

type vreg = int

type value =
  | VReg of vreg
  | VImm of int

type instr =
  | Binop of vreg * binop * value * value
  | Unop  of vreg * uop * value
  | Li    of vreg * int
  | Mov   of vreg * value
  | Lw    of vreg * vreg * int
  | Sw    of vreg * int * value
  | La    of vreg * string
  | Call  of vreg * string * value list
  | Ret   of value option
  | Jmp   of string
  | Bz    of value * string
  | Bnz   of value * string
  | Label of string

type func_ir = {
  fir_name     : string;
  fir_params   : (string * int) list;
  fir_locals   : (string * int) list;
  fir_stack_sz : int;
  fir_ret_type : type_kind;
  fir_body     : instr list;
}

type module_ir = {
  mir_globals   : (string * int) list;
  mir_functions : func_ir list;
}

let string_of_binop = function
  | Add -> "add"  | Sub -> "sub"  | Mul -> "mul"  | Div -> "div"  | Mod -> "rem"
  | Eq  -> "seq"  | Neq -> "sne"  | Lt  -> "slt"  | Gt  -> "sgt"
  | Le  -> "sle"  | Ge  -> "sge"
  | _ -> "??"

let string_of_uop = function
  | Neg -> "neg"  | Pos -> "mov"  | Not -> "not"

let string_of_value = function
  | VReg r -> "%" ^ string_of_int r
  | VImm n -> string_of_int n

let string_of_instr = function
  | Binop (rd, op, v1, v2) ->
    Printf.sprintf "  %%%d = %s %s, %s" rd (string_of_binop op)
      (string_of_value v1) (string_of_value v2)
  | Unop (rd, op, v) ->
    Printf.sprintf "  %%%d = %s %s" rd (string_of_uop op) (string_of_value v)
  | Li (rd, n) ->
    Printf.sprintf "  %%%d = li %d" rd n
  | Mov (rd, v) ->
    Printf.sprintf "  %%%d = mov %s" rd (string_of_value v)
  | Lw (rd, base, off) ->
    Printf.sprintf "  %%%d = lw [%%%d + %d]" rd base off
  | Sw (base, off, v) ->
    Printf.sprintf "  sw [%%%d + %d], %s" base off (string_of_value v)
  | La (rd, name) ->
    Printf.sprintf "  %%%d = la @%s" rd name
  | Call (rd, name, args) ->
    let args_str = String.concat ", " (List.map string_of_value args) in
    Printf.sprintf "  %%%d = call @%s(%s)" rd name args_str
  | Ret (Some v) ->
    Printf.sprintf "  ret %s" (string_of_value v)
  | Ret None ->
    "  ret"
  | Jmp label ->
    Printf.sprintf "  jmp %s" label
  | Bz (v, label) ->
    Printf.sprintf "  bz %s, %s" (string_of_value v) label
  | Bnz (v, label) ->
    Printf.sprintf "  bnz %s, %s" (string_of_value v) label
  | Label name ->
    Printf.sprintf "%s:" name

let print_func f =
  let ret_str = match f.fir_ret_type with Int -> "int" | Void -> "void" in
  Printf.printf "\nfunc @%s : %s\n" f.fir_name ret_str;
  if f.fir_params <> [] then begin
    Printf.printf "  params:\n";
    List.iter (fun (n, off) ->
      Printf.printf "    %s [sp+%d]\n" n off) f.fir_params
  end;
  if f.fir_locals <> [] then begin
    Printf.printf "  locals:\n";
    List.iter (fun (n, off) ->
      Printf.printf "    %s [sp+%d]\n" n off) f.fir_locals
  end;
  Printf.printf "  stack_size: %d\n" f.fir_stack_sz;
  Printf.printf "  body:\n";
  List.iter (fun i -> Printf.printf "%s\n" (string_of_instr i)) f.fir_body

let print_module (m : module_ir) =
  if m.mir_globals <> [] then begin
    Printf.printf "globals:\n";
    List.iter (fun (name, init) ->
      Printf.printf "  @%s = %d\n" name init) m.mir_globals
  end;
  List.iter print_func m.mir_functions
