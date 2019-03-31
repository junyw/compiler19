test: expr.ml sexp.ml test.ml
	ocamlfind ocamlc -o test -package extlib,oUnit,str -linkpkg -g expr.ml sexp.ml test.ml
	./test

clean:
	rm -f test *.log *.cmi *.cmo *.cache *.zip

zip:
	zip submission.zip Makefile sexp.ml expr.ml test.ml
