all:
	ocamlbuild -lib str add_comments.byte
	make -C ../..
	./test_script basic_type.lem
	./test_script basic_exprs.lem
	./test_script basic_pats.lem
	./test_script basic_defs.lem
	./test_script basic_typedefs.lem
	./test_script identifiers.lem
	./test_script classes.lem
	./test_script do_notation.lem

clean:
	-ocamlbuild -clean
	-rm -f test.lem
