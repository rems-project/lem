DEPENDS ?= dependencies
ZARITH ?= $(DEPENDS)/zarith
override OCAMLFLAGS += -g



BUILD_DEPS := $(if $(shell ocamlfind ocamlc -package zarith 2>&1),true,false)
ifeq ("$(BUILD_DEPS)","true")
  # build dependencies from source
  DEPS  = -I $(ZARITH) zarith$(suffix $@) nums$(suffix $@)
  DEPSPREREQ = dependencies
else
  # use preinstalled packages (to get the package do 'opam install zarith')
  DEPS  = -package zarith -package num -linkpkg
endif

BIG_INT_IMPL_ML ?= big_int_impl.ml
BIG_INT_IMPL_MLI ?= big_int_impl.mli

ML_FILES := \
	lem.ml lem_assert_extra.ml lem_bool.ml lem_basic_classes.ml lem_function.ml lem_maybe.ml lem_tuple.ml lem_num.ml lem_list.ml lem_either.ml \
	lem_list_extra.ml lem_set_helpers.ml lem_set.ml lem_map.ml lem_map_extra.ml lem_maybe_extra.ml lem_function_extra.ml \
	lem_relation.ml lem_sorting.ml lem_set_extra.ml \
	lem_string.ml lem_string_extra.ml lem_word.ml lem_show.ml lem_show_extra.ml lem_pervasives.ml lem_num_extra.ml lem_machine_word.ml lem_pervasives_extra.ml

SUPPORTING_ML_FILES := \
	$(BIG_INT_IMPL_MLI) $(BIG_INT_IMPL_ML) nat_big_num.mli nat_big_num.ml nat_num.mli nat_num.ml pset.mli pset.ml pmap.mli pmap.ml vector.mli vector.ml bit.mli bit.ml xstring.mli xstring.ml either.ml

CMX_FILES := $(patsubst %.ml,%.cmx,$(ML_FILES))
CMO_FILES := $(patsubst %.ml,%.cmo,$(ML_FILES))
SUPPORTING_CMX_FILES := $(patsubst %.ml,%.cmx,$(SUPPORTING_ML_FILES))
SUPPORTING_CMO_FILES := $(patsubst %.ml,%.cmo,$(SUPPORTING_ML_FILES))

all: extract.cmxa extract.cma

extract.cmxa: $(SUPPORTING_ML_FILES) $(ML_FILES) $(DEPSPREREQ)
	ocamlfind ocamlopt $(OCAMLFLAGS) $(DEPS) $(SUPPORTING_ML_FILES) $(ML_FILES)
	ocamlfind ocamlopt $(OCAMLFLAGS) -a -o $@ $(SUPPORTING_CMX_FILES) $(CMX_FILES)

extract.cma: $(SUPPORTING_ML_FILES) $(ML_FILES) $(DEPSPREREQ)
	ocamlfind ocamlc $(OCAMLFLAGS) $(DEPS) $(SUPPORTING_ML_FILES) $(ML_FILES)
	ocamlfind ocamlc $(OCAMLFLAGS) -a -o $@ $(SUPPORTING_CMO_FILES) $(CMO_FILES)

local_clean:
	\rm -f *.c* *.o *.cma *.cmxa *.a

clean: local_clean
	make -C dependencies clean

dependencies:
	make -C dependencies

.PHONY: all local_clean clean dependencies
