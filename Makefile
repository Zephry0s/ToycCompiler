.PHONY: all clean

all: toyc

toyc: src/lexer.ml
	cd src && ocamlc -c token.ml
	cd src && ocamlc -c ast.ml
	cd src && ocamlc -c print_ast.ml
	cd src && ocamlc -c lexer.ml
	cd src && ocamlc -c parser.ml
	cd src && ocamlc -c semant.ml
	cd src && ocamlc -c ir.ml
	cd src && ocamlc -c irgen.ml
	cd src && ocamlc -c reg_alloc.ml
	cd src && ocamlc -c codegen.ml
	cd src && ocamlc -c main.ml
	cd src && ocamlc -o ../toyc token.cmo ast.cmo print_ast.cmo lexer.cmo parser.cmo semant.cmo ir.cmo irgen.cmo reg_alloc.cmo codegen.cmo main.cmo

src/lexer.ml: src/lexer.mll src/token.ml
	cd src && ocamlc -c token.ml && ocamllex lexer.mll

clean:
	rm -f src/lexer.ml src/*.cmi src/*.cmo toyc
