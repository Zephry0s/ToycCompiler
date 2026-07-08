let parse_channel ch filename _opt =
  let lexbuf = Lexing.from_channel ch in
  Lexing.set_filename lexbuf filename;
  try
    let ast = Parser.comp_unit Lexer.token lexbuf in
    let symtab = Semant.check_comp_unit ast in
    let module_ir = Irgen.gen_module symtab ast in
    Codegen.gen module_ir;
    0
  with
  | Lexer.LexError msg ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "Lex error: %s: line %d, col %d: %s\n"
        filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) msg;
      1
  | Parser.Error msg ->
      Printf.eprintf "Parse error: %s: %s\n" filename msg;
      1
  | Failure msg ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "Error: %s: line %d, col %d: %s\n"
        filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) msg;
      1

let () =
  let opt_enabled = ref false in
  let filename = ref None in
  let rec parse_args = function
    | [] -> ()
    | "-opt" :: rest -> opt_enabled := true; parse_args rest
    | f :: rest -> filename := Some f; parse_args rest
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  let code =
    match !filename with
    | None ->
        parse_channel stdin "<stdin>" !opt_enabled
    | Some f ->
        let ch = open_in f in
        let result = parse_channel ch f !opt_enabled in
        close_in ch;
        result
  in
  exit code
