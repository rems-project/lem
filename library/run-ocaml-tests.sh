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
  ocamlfind ocamlc -package zarith -linkpkg -dllpath-all -o ${file_nat} -I ocaml-lib/_build_zarith extract.cma ${file}
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
