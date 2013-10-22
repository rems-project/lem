poly_lib = $(dir $(shell which poly))../lib/

all: lem holtests ocamltests 

lem:
	make -C ../..

holtests: TypesTheory.uo PatsTheory.uo ExpsTheory.uo HoltestTheory.uo

coqtests: types.vo pats.vo exps.vo 

ocamltests: types.byte pats.byte exps.byte classes.byte

isabelletests: isatests/Pats.thy isatests/Types.thy isatests/Exps.thy
	isabelle make clean
	isabelle make isatests

%.ml: %.lem ../../lem
	../../lem -wl ign -ocaml $<

TypesScript.sml: types.lem ../../lem
	../../lem -wl ign -hol $<

PatsScript.sml: pats.lem ../../lem
	../../lem -wl ign -hol $<

ExpsScript.sml: exps.lem ../../lem
	../../lem -wl ign -hol $<

HoltestScript.sml: holtest.lem ../../lem
	../../lem -wl ign -hol $<

%.v: %.lem ../../lem
	../../lem -wl ign -coq $<

Types.thy: types.lem ../../lem
	../../lem -wl ign -isa $<

Pats.thy: pats.lem ../../lem
	../../lem -wl ign -isa $<

Exps.thy: exps.lem ../../lem
	../../lem -wl ign -isa $<

%Theory.uo: %Script.sml hol_preload
	Holmake --poly ./hol_preload --qof --quiet $@

%.vo: %.v
	coqc $<

extract.cma:
	make -C ../../ocaml-lib

%.byte: %.ml $(CURDIR)/../../ocaml-lib/_build/extract.cma
	ocamlc.opt -I $(CURDIR)/../../ocaml-lib/_build -o $@ extract.cma $<

HolDoc.uo HolDoc.ui: HolDoc.sml HolDoc.sig
	Holmake HolDoc.uo

hol_preload.o: HolDoc.uo HolDoc.ui hol_preload.ml
	hol.builder < hol_preload.ml

hol_preload: hol_preload.o
	gcc -L$(poly_lib) -o hol_preload -lpolymain -lpolyml -segprot POLY rwx rwx hol_preload.o

isatests/%.thy: %.thy
	cp $< $@

clean:
	-Holmake cleanAll
	-isabelle make clean
	-rm -fr hol_preload *.cmi *.cmo *.byte pats.ml *.uo *.ui *.v *.thy *Theory.* *Script.* *.imn hol_preload.o exps.ml classes.ml types.ml _build isatests/*.thy holtest.ml

.precious: PatsScript.sml pats.ml ExpsScript.sml exps.ml classes.ml TypesScript.sml types.ml types.v Exps.thy exps.v Pats.thy Types.thy types.v HolScript.sml
