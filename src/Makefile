all:
	ocamlbuild -use-ocamlfind -cflags -g main.native
#	ocamlbuild main.native

profile:
	ocamlbuild -cflags -g main.p.native

doc:
	mkdir -p html-doc
	ocamlfind ocamldoc -package zarith -I _build/ -I _build/ulib/ *.mli finite_map.ml -sort -html -d html-doc

doc-pdf:
	mkdir -p tex-doc
	ocamlfind ocamldoc -package zarith -I _build/ -I _build/ulib/ *.mli finite_map.ml -latex -sort -d tex-doc -o tex-doc/lem-doc.tex; true
	cd tex-doc; pdflatex lem-doc.tex

doc-dot:
	ocamlfind ocamldoc -package zarith -I _build/ -I _build/ulib/ *.ml *.mli ulib/*.mli ulib/*.ml -dot -sort -d tex-doc -dot-reduce -o dep.dot; true
	dot -Tpdf -o dep.pdf dep.dot

debug: 
	ocamlbuild -tag annot main.d.byte

clean:
	-ocamlbuild -clean
	-rm -rf main.native
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
