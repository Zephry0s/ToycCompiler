{
open Token
exception LexError of string
}

let whitespace = [' ' '\t' '\r']+
let digit      = ['0'-'9']
let nonzero    = ['1'-'9']
let alpha      = ['A'-'Z' 'a'-'z']
let ident_char = ['A'-'Z' 'a'-'z' '0'-'9' '_']

rule token = parse
  | whitespace   { token lexbuf }
  | '\n'         { Lexing.new_line lexbuf; token lexbuf }

  | "//"         { line_comment lexbuf }
  | "/*"         { block_comment 0 lexbuf }

  | "const"      { CONST }
  | "int"        { INT }
  | "void"       { VOID }
  | "if"         { IF }
  | "else"       { ELSE }
  | "while"      { WHILE }
  | "break"      { BREAK }
  | "continue"   { CONTINUE }
  | "return"     { RETURN }

  | "<="         { LE }
  | ">="         { GE }
  | "=="         { EQEQ }
  | "!="         { NEQ }
  | "&&"         { AMPAMP }
  | "||"         { PIPEPIPE }
  | "+"          { PLUS }
  | "-"          { MINUS }
  | "*"          { STAR }
  | "/"          { SLASH }
  | "%"          { PERCENT }
  | "!"          { BANG }
  | "="          { ASSIGN }
  | "<"          { LT }
  | ">"          { GT }

  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "{"          { LBRACE }
  | "}"          { RBRACE }
  | ","          { COMMA }
  | ";"          { SEMICOLON }

  | (alpha | '_') ident_char*
      { ID (Lexing.lexeme lexbuf) }

  | '0'          { NUMBER 0 }
  | nonzero digit*
      { NUMBER (int_of_string (Lexing.lexeme lexbuf)) }

  | eof          { EOF }

  | _ as c {
      let msg = Printf.sprintf "unexpected character '%c'" c in
      raise (LexError msg)
    }

and line_comment = parse
  | '\n'  { Lexing.new_line lexbuf; token lexbuf }
  | eof   { EOF }
  | _     { line_comment lexbuf }

and block_comment depth = parse
  | "/*"  { block_comment (depth + 1) lexbuf }
  | "*/"  { if depth = 0 then token lexbuf
            else block_comment (depth - 1) lexbuf }
  | '\n'  { Lexing.new_line lexbuf; block_comment depth lexbuf }
  | eof   { raise (LexError "unterminated block comment") }
  | _     { block_comment depth lexbuf }
