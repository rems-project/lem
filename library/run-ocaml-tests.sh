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
  ocamlfind ocamlc -o ${file_nat} -I ocaml-lib/dependencies/zarith/ -I ocaml-lib zarith.cma nums.cma extract.cma ${file}
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



