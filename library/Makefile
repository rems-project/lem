LIBS=bool.lem basic_classes.lem function.lem maybe.lem num.lem tuple.lem list.lem either.lem set_helpers.lem set.lem map.lem relation.lem sorting.lem function_extra.lem assert_extra.lem list_extra.lem string.lem num_extra.lem map_extra.lem set_extra.lem maybe_extra.lem string_extra.lem word.lem show.lem show_extra.lem machine_word.lem pervasives.lem pervasives_extra.lem debug.lem

NOW:=$(shell date +%Y-%m-%d---%H-%M-%S)
OCAML_BUILD_DIR=ocaml-build-dir---${NOW}
HOL_BUILD_DIR=hol-build-dir---${NOW}
ISA_BUILD_DIR=isa-build-dir---${NOW}

OCAML_BUILD_DIR_REUSED=ocaml-build-dir-reused
HOL_BUILD_DIR_REUSED=hol-build-dir-reused
ISA_BUILD_DIR_REUSED=isa-build-dir-reused


markdown_targets := $(patsubst %.markdown,%.html,$(wildcard *.markdown))

libs : ocaml-libs hol-libs isa-libs coq-libs tex-libs html-libs

.PHONY: ../lem
../lem:
	$(MAKE) -C .. build-lem

hol-libs: ../lem
	../lem -hol -hol_remove_matches -outdir ../hol-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

ocaml-libs: ../lem
	../lem -ocaml -outdir ../ocaml-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

isa-libs: ../lem
	../lem -isa -outdir ../isabelle-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

coq-libs: ../lem
	../lem -coq -outdir ../coq-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output

tex-libs: ../lem
	../lem -tex_all ../tex-lib/lem-libs.tex -wl ign -wl_auto_import err ${LIBS} 

html-libs: ../lem
	../lem -html -outdir ../html-lib -wl ign -wl_auto_import err ${LIBS} 

ocaml-lib-tests: 
	@mkdir -p ${OCAML_BUILD_DIR}
	@rm -rf ocaml-build-dir
	@ln -s ${OCAML_BUILD_DIR} ocaml-build-dir
	@../lem -ocaml -outdir ${OCAML_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -only_changed_output -no_dep_reorder
	@./run-ocaml-tests.sh ${OCAML_BUILD_DIR}

ocaml-lib-tests-reuse: 
	@mkdir -p ${OCAML_BUILD_DIR_REUSED} || true
	@../lem -ocaml -outdir ${OCAML_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -only_changed_output -no_dep_reorder
	@./run-ocaml-tests.sh ${OCAML_BUILD_DIR_REUSED}

hol-lib-tests: 
	@mkdir -p ${HOL_BUILD_DIR}
	@rm -f hol-build-dir
	@ln -s ${HOL_BUILD_DIR} hol-build-dir       
	@../lem -hol -outdir ${HOL_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output -no_dep_reorder
	@cp Holmakefile ${HOL_BUILD_DIR}
	@cd ${HOL_BUILD_DIR}; Holmake 

hol-lib-tests-reuse: 
	@mkdir -p ${HOL_BUILD_DIR_REUSED} || true
	@../lem -hol -outdir ${HOL_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output -no_dep_reorder
	@cp Holmakefile ${HOL_BUILD_DIR_REUSED}
	@cd ${HOL_BUILD_DIR_REUSED}; Holmake 

# The tests are generated from the same files as the library, but are run in a
# separate Isabelle session, so we manually patch up the names with sed.
isa-lib-tests: 
	@mkdir -p ${ISA_BUILD_DIR}
	@rm -f isa-build-dir
	@ln -s ${ISA_BUILD_DIR} isa-build-dir       
	@../lem -isa -outdir ${ISA_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output -no_dep_reorder
	@sed -i -e 's/^  "Lem_/  "LEM.Lem_/' -e 's/^  "Lem"/  "LEM.Lem"/' ${ISA_BUILD_DIR}/Lem_*Auxiliary.thy
	@./gen-isa-tests.sh ${ISA_BUILD_DIR} 
	@echo "please run\n   isabelle jedit -d ../isabelle-lib -l LEM ${ISA_BUILD_DIR}/LemTests.thy"

isa-lib-tests-reuse: 
	@mkdir -p ${ISA_BUILD_DIR_REUSED} || true
	@../lem -isa -outdir ${ISA_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output -no_dep_reorder
	@sed -i -e 's/^  "Lem_/  "LEM.Lem_/' -e 's/^  "Lem"/  "LEM.Lem"/' ${ISA_BUILD_DIR}/Lem_*Auxiliary.thy
	@./gen-isa-tests.sh ${ISA_BUILD_DIR_REUSED} 
	@echo "please run\n   isabelle jedit ${ISA_BUILD_DIR_REUSED}/LemTests.thy"


markdown: $(markdown_targets)

%.html : %.markdown
	markdown $< > $@

clean:
	rm -rf ocaml-build-dir*
	rm -rf hol-build-dir*
	rm -rf isa-build-dir*
