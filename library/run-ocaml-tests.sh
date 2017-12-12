#!/bin/sh -e

dir=$1
file=list
cd $dir

rm -f ocaml-lib
ln -s ../../ocaml-lib .

# OCaml foolishly provides "its own" LD_LIBRARY_PATH, but the vanilla one
# also takes effect if the OCaml one is not set. So we have to munge both.
export LD_LIBRARY_PATH="$(readlink -f ocaml-lib)"/dependencies/zarith/:"${LD_LIBRARY_PATH}"
export CAML_LD_LIBRARY_PATH="$(readlink -f ocaml-lib)"/dependencies/zarith/:"${CAML_LD_LIBRARY_PATH}"

for file in *Auxiliary.ml
do
  echo $file
  file_nat=${file%.ml}.native
  ocamlfind ocamlc -o ${file_nat} -I ocaml-lib/dependencies/zarith/ -I ocaml-lib zarith.cma nums.cma extract.cma ${file}
done 

for file in *.native 
do
  file_name=`basename $file`
  file_name=${file_name%Auxiliary.native}
  echo "\n\n\n"
  echo "***************************************************"
  echo "* Testing ${file_name}"
  echo "***************************************************\n"
  ./$file
done



