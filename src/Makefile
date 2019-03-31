UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  FORMAT=aout
  PIE=
else
ifeq ($(UNAME), Darwin)
  FORMAT=macho
  PIE=
endif
endif

PKGS=oUnit,extlib,unix,batteries
BUILD=ocamlbuild -r -use-ocamlfind -ocamlyacc 'ocamlyacc -v'

main: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) main.native
	mv main.native main

test: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) test.native
	mv test.native test

output/%.run: output/%.o main.c gc.o
	clang $(PIE) -mstackrealign -g -m32 -o $@ gc.o main.c $<

output/%.o: output/%.s
	nasm -f $(FORMAT) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.garter main
	./main $< > $@

gc.o: gc.c gc.h
	gcc gc.c -m32 -c -g -o gc.o

clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log *.o
	rm -rf _build/
	rm -f main test
