#!/bin/sh -e

dir=$1
file=list
cd $dir

rm -f ocaml-lib
ln -s ../../ocaml-lib .

for file in *Auxiliary.ml
do
  echo $file
  file_nat=${file%.ml}.native
  ocamlfind ocamlc -o ${file_nat} -I ocaml-lib/dependencies/zarith/ -I ocaml-lib zarith.cma nums.cma lem.cmo either.cmo nat_num.cmo lem_function.cmo lem_list.cmo big_int_impl.cmo nat_big_num.cmo lem_num.cmo lem_list_extra.cmo pset.cmo pmap.cmo lem_basic_classes.cmo lem_map.cmo lem_relation.cmo lem_maybe.cmo lem_set.cmo lem_set_extra.cmo lem_sorting.cmo xstring.cmo lem_string_extra.cmo lem_word.cmo ${file}
done 

for file in *.native 
do
  file_name=`basename $file`
  file_name=${file_name%Auxiliary.native}
  echo -e "\n\n\n"
  echo -e "***************************************************"
  echo -e "* Testing ${file_name}"
  echo -e "***************************************************\n"
  ./$file
done



