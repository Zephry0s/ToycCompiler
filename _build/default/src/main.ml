let parse_channel ch filename =
  let lexbuf = Lexing.from_channel ch in
  Lexing.set_filename lexbuf filename;
  try
    let ast = Parser.comp_unit Lexer.token lexbuf in
    Print_ast.print_comp_unit ast;
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
  let code =
    match Sys.argv with
    | [| _ |] ->
        parse_channel stdin "<stdin>"
    | [| _; filename |] ->
        let ch = open_in filename in
        let result = parse_channel ch filename in
        close_in ch;
        result
    | _ ->
        Printf.eprintf "Usage: %s [file.tc]\n" Sys.argv.(0);
        1
  in
  exit code
