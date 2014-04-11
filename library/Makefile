LIBS=pervasives_extra.lem pervasives.lem basic_classes.lem either.lem function.lem list.lem map.lem maybe.lem relation.lem set_helpers.lem sorting.lem tuple.lem function_extra.lem bool.lem list_extra.lem num.lem map_extra.lem set.lem set_extra.lem maybe_extra.lem string.lem string_extra.lem word.lem assert_extra.lem

NOW=$(shell date +%Y-%m-%d---%H-%M-%S)
OCAML_BUILD_DIR=ocaml-build-dir---${NOW}
HOL_BUILD_DIR=hol-build-dir---${NOW}
ISA_BUILD_DIR=isa-build-dir---${NOW}

OCAML_BUILD_DIR_REUSED=ocaml-build-dir-reused
HOL_BUILD_DIR_REUSED=hol-build-dir-reused
ISA_BUILD_DIR_REUSED=isa-build-dir-reused


markdown_targets := $(patsubst %.markdown,%.html,$(wildcard *.markdown))

libs : ocaml-libs hol-libs isa-libs coq-libs 

hol-libs:
	make -C .. build-lem
	../lem -hol -hol_remove_matches -outdir ../hol-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

ocaml-libs:
	make -C .. build-lem
	../lem -ocaml -outdir ../ocaml-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

isa-libs:
	make -C .. build-lem
	../lem -isa -outdir ../isabelle-lib -wl ign -wl_auto_import err -wl_rename err ${LIBS} -auxiliary_level none -only_changed_output

coq-libs:
	make -C .. build-lem
	../lem -coq -outdir ../coq-lib -wl ign -wl_auto_import err ${LIBS} -auxiliary_level none -only_changed_output

tex-libs:
	make -C .. build-lem
	../lem -tex_all ../tex-lib/lem-libs.tex -wl ign -wl_auto_import err ${LIBS} 

html-libs:
	make -C .. build-lem
	../lem -html -outdir ../html-lib -wl ign -wl_auto_import err ${LIBS} 

ocaml-lib-tests: 
	@mkdir -p ${OCAML_BUILD_DIR}
	@rm -f ocaml-build-dir
	@ln -s ${OCAML_BUILD_DIR} ocaml-build-dir       
	@../lem -ocaml -outdir ${OCAML_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -only_changed_output
	@./run-ocaml-tests.sh ${OCAML_BUILD_DIR}

ocaml-lib-tests-reuse: 
	@mkdir -p ${OCAML_BUILD_DIR_REUSED} || true
	@../lem -ocaml -outdir ${OCAML_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -only_changed_output
	@./run-ocaml-tests.sh ${OCAML_BUILD_DIR_REUSED}

hol-lib-tests: 
	@mkdir -p ${HOL_BUILD_DIR}
	@rm -f hol-build-dir
	@ln -s ${HOL_BUILD_DIR} hol-build-dir       
	@../lem -hol -outdir ${HOL_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output
	@cp Holmakefile ${HOL_BUILD_DIR}
	@cd ${HOL_BUILD_DIR}; Holmake 

hol-lib-tests-reuse: 
	@mkdir -p ${HOL_BUILD_DIR_REUSED} || true
	@../lem -hol -outdir ${HOL_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output
	@cp Holmakefile ${HOL_BUILD_DIR_REUSED}
	@cd ${HOL_BUILD_DIR_REUSED}; Holmake 

isa-lib-tests: 
	@mkdir -p ${ISA_BUILD_DIR}
	@rm -f isa-build-dir
	@ln -s ${ISA_BUILD_DIR} isa-build-dir       
	@../lem -isa -outdir ${ISA_BUILD_DIR} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output
	@./gen-isa-tests.sh ${ISA_BUILD_DIR} 
	@echo "please run\n   isabelle jedit ${ISA_BUILD_DIR}/LemTests.thy"

isa-lib-tests-reuse: 
	@mkdir -p ${ISA_BUILD_DIR_REUSED} || true
	@../lem -isa -outdir ${ISA_BUILD_DIR_REUSED} -wl ign -wl_auto_import err -wl_rename err ${LIBS} -only_auxiliary -auxiliary_level auto -only_changed_output
	@./gen-isa-tests.sh ${ISA_BUILD_DIR_REUSED} 
	@echo "please run\n   isabelle jedit ${ISA_BUILD_DIR_REUSED}/LemTests.thy"


markdown: $(markdown_targets)

%.html : %.markdown
	markdown $< > $@

clean:
	rm -rf ocaml-build-dir*
	rm -rf hol-build-dir*
	rm -rf isa-build-dir*
