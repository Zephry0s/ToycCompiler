open Ir
open Ast

let align16 n = (n + 15) / 16 * 16

let vreg_off stack_sz n = stack_sz + n * 4

let load_val reg stack_sz = function
  | VReg r -> Printf.sprintf "  lw %s, %d(sp)\n" reg (vreg_off stack_sz r)
  | VImm n -> Printf.sprintf "  li %s, %d\n" reg n

let rec max_vreg_instr m = function
  | Binop (rd, _, v1, v2) ->
    let m = max m rd in
    let m = match v1 with VReg r -> max m r | _ -> m in
    let m = match v2 with VReg r -> max m r | _ -> m in
    m
  | Unop (rd, _, v) ->
    let m = max m rd in
    (match v with VReg r -> max m r | _ -> m)
  | Li (rd, _) | Mov (rd, _) | Lw (rd, _, _) | La (rd, _) ->
    max m rd
  | Sw (base, _, v) ->
    let m = max m base in
    (match v with VReg r -> max m r | _ -> m)
  | Call (rd, _, args) ->
    let m = max m rd in
    List.fold_left (fun m v -> match v with VReg r -> max m r | _ -> m) m args
  | Ret (Some v) ->
    (match v with VReg r -> max m r | _ -> m)
  | Ret None -> m
  | Jmp _ | Label _ -> m
  | Bz (v, _) -> (match v with VReg r -> max m r | _ -> m)
  | Bnz (v, _) -> (match v with VReg r -> max m r | _ -> m)

let max_vreg instrs = List.fold_left max_vreg_instr 0 instrs

let riscv_binop = function
  | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div" | Mod -> "rem"
  | _ -> "??"

let emit_one buf stack_sz = function
  | Binop (rd, Eq, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  sub t0, t0, t1\n  seqz t0, t0\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, Neq, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  sub t0, t0, t1\n  snez t0, t0\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, Lt, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  slt t0, t0, t1\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, Gt, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  slt t0, t1, t0\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, Le, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  slt t0, t1, t0\n  xori t0, t0, 1\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, Ge, v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf "  slt t0, t0, t1\n  xori t0, t0, 1\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop (rd, (Add | Sub | Mul | Div | Mod as op), v1, v2) ->
    Buffer.add_string buf (load_val "t0" stack_sz v1);
    Buffer.add_string buf (load_val "t1" stack_sz v2);
    Buffer.add_string buf (Printf.sprintf "  %s t0, t0, t1\n" (riscv_binop op));
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Binop _ -> ()
  | Unop (rd, Neg, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf "  neg t0, t0\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Unop (rd, Not, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf "  seqz t0, t0\n";
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Unop (rd, Pos, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Li (rd, n) ->
    Buffer.add_string buf (Printf.sprintf "  li t0, %d\n" n);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Mov (rd, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Lw (rd, 0, off) ->
    Buffer.add_string buf (Printf.sprintf "  lw t0, %d(sp)\n" off);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Lw (rd, base, off) ->
    Buffer.add_string buf (Printf.sprintf "  lw t0, %d(sp)\n" (vreg_off stack_sz base));
    Buffer.add_string buf (Printf.sprintf "  lw t0, %d(t0)\n" off);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Sw (0, off, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" off)
  | Sw (base, off, v) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  lw t1, %d(sp)\n" (vreg_off stack_sz base));
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(t1)\n" off)
  | La (rd, name) ->
    Buffer.add_string buf (Printf.sprintf "  la t0, %s\n" name);
    Buffer.add_string buf (Printf.sprintf "  sw t0, %d(sp)\n" (vreg_off stack_sz rd))
  | Call (rd, fname, args) ->
    List.iteri (fun i v ->
      if i < 8 then begin
        let reg = "a" ^ string_of_int i in
        Buffer.add_string buf (load_val reg stack_sz v)
      end
    ) args;
    Buffer.add_string buf (Printf.sprintf "  jal ra, %s\n" fname);
    Buffer.add_string buf (Printf.sprintf "  sw a0, %d(sp)\n" (vreg_off stack_sz rd))
  | Ret _ -> ()
  | Jmp label ->
    Buffer.add_string buf (Printf.sprintf "  j %s\n" label)
  | Bz (v, label) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  beqz t0, %s\n" label)
  | Bnz (v, label) ->
    Buffer.add_string buf (load_val "t0" stack_sz v);
    Buffer.add_string buf (Printf.sprintf "  bnez t0, %s\n" label)
  | Label name ->
    Buffer.add_string buf (Printf.sprintf "%s:\n" name)

let emit_epilogue buf ra_off total_frame =
  Buffer.add_string buf (Printf.sprintf "  lw ra, %d(sp)\n" ra_off);
  Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" total_frame);
  Buffer.add_string buf "  ret\n"

let emit_func buf f =
  let stack_sz = f.fir_stack_sz in
  let mv = max_vreg f.fir_body in
  let n_params = List.length f.fir_params in
  let max_v = max mv n_params in
  let unaligned = stack_sz + (max_v + 1) * 4 + 4 in
  let total = align16 unaligned in
  let ra_off = total - 4 in

  let ret_label = "." ^ f.fir_name ^ "_ret" in

  Buffer.add_string buf (Printf.sprintf "\n  .globl %s\n" f.fir_name);
  Buffer.add_string buf (Printf.sprintf "%s:\n" f.fir_name);
  Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" (-total));
  Buffer.add_string buf (Printf.sprintf "  sw ra, %d(sp)\n" ra_off);

  for i = 0 to n_params - 1 do
    Buffer.add_string buf
      (Printf.sprintf "  sw a%d, %d(sp)\n" i (vreg_off stack_sz (i+1)))
  done;

  List.iter (function
    | Ret (Some v) ->
      Buffer.add_string buf (load_val "a0" stack_sz v);
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label)
    | Ret None ->
      Buffer.add_string buf (Printf.sprintf "  j %s\n" ret_label)
    | instr ->
      emit_one buf stack_sz instr
  ) f.fir_body;

  Buffer.add_string buf (Printf.sprintf "%s:\n" ret_label);
  if f.fir_name = "main" then begin
    Buffer.add_string buf (Printf.sprintf "  lw ra, %d(sp)\n" ra_off);
    Buffer.add_string buf (Printf.sprintf "  addi sp, sp, %d\n" total);
    Buffer.add_string buf "  li a7, 10\n";
    Buffer.add_string buf "  ecall\n"
  end else
    emit_epilogue buf ra_off total

let emit_globals buf globals =
  if globals <> [] then begin
    Buffer.add_string buf ".data\n";
    List.iter (fun (name, init) ->
      Buffer.add_string buf (Printf.sprintf "  .globl %s\n" name);
      Buffer.add_string buf (Printf.sprintf "%s: .word %d\n" name init)
    ) globals;
    Buffer.add_string buf "\n"
  end

let gen (m : module_ir) =
  let buf = Buffer.create 65536 in
  emit_globals buf m.mir_globals;
  Buffer.add_string buf ".text\n";
  List.iter (emit_func buf) m.mir_functions;
  print_string (Buffer.contents buf)
