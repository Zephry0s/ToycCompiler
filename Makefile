.PHONY: all clean

all: toyc

toyc: src/lexer.ml
	cd src && ocamlc -c token.ml
	cd src && ocamlc -c ast.ml
	cd src && ocamlc -c print_ast.ml
	cd src && ocamlc -c lexer.ml
	cd src && ocamlc -c parser.ml
	cd src && ocamlc -c main.ml
	cd src && ocamlc -o ../toyc token.cmo ast.cmo print_ast.cmo lexer.cmo parser.cmo main.cmo

src/lexer.ml: src/lexer.mll src/token.ml
	cd src && ocamlc -c token.ml && ocamllex lexer.mll

clean:
	rm -f src/lexer.ml src/*.cmi src/*.cmo toyc
