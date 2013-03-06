all:
	make -C ../..
	rm -f results
	ocamlbuild -lib unix -lib str tester.byte
	./tester.byte < tests
	chmod a-w results
	diff results results_checked

clean:
	-ocamlbuild -clean
	-rm -f results test.lem testScript.sml
