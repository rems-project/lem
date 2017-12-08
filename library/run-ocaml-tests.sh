#!/bin/sh -e

dir=$1
file=list
cd $dir

rm -f ocaml-lib
ln -s ../../ocaml-lib .

export LD_LIBRARY_PATH="$(readlink -f ocaml-lib)"/dependencies/zarith/:"${LD_LIBRARY_PATH}"

for file in *Auxiliary.ml
do
  echo $file
  file_nat=${file%.ml}.native
  if ocamlfind ocamlc -package zarith 2>&1 > /dev/null; then
    ocamlfind ocamlc -o ${file_nat} -package zarith -linkpkg -I ocaml-lib nums.cma extract.cma ${file}
  else
    ocamlfind ocamlc -o ${file_nat} -I ocaml-lib/dependencies/zarith/ -I ocaml-lib zarith.cma nums.cma extract.cma ${file}
  fi
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



