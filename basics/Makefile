test: functions.ml test.ml
	ocamlfind ocamlc -o test -package oUnit -linkpkg -g functions.ml test.ml
	./test
	
clean:
	rm -f test *.log *.cmi *.cmo *.cache *.zip

zip:
	zip submission.zip Makefile functions.ml test.ml
