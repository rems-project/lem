LIBS=pervasives_extra.lem pervasives.lem basic_classes.lem either.lem function.lem list.lem map.lem maybe.lem relation.lem set_helpers.lem sorting.lem tuple.lem function_extra.lem bool.lem list_extra.lem num.lem map_extra.lem set.lem set_extra.lem maybe_extra.lem

markdown_targets := $(patsubst %.markdown,%.html,$(wildcard *.markdown))

libs : ocaml-libs hol-libs isa-libs 

hol-libs:
	../lem -hol -outdir ../hol-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output

ocaml-libs:
	../lem -ocaml -outdir ../ocaml-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output

isa-libs:
	../lem -isa -outdir ../isabelle-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output

coq-libs:
	make -C ..
	../lem -coq -outdir ../coq-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output


markdown: $(markdown_targets)

%.html : %.markdown
	markdown $< > $@

