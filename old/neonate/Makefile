%.run: %.o
	clang -m64 -o $@ main.c $<
%.o: %.s
	nasm -f macho64 -o $@ $<

%.s: %.int
	ocaml compiler.ml $< > $@
	
clean:
	rm -f our_code *.o *.run *.s
