#!/bin/bash

dir=$1
file=list
cd $dir

rm -f ocaml-lib
ln -s ../../ocaml-lib .

for file in *Auxiliary.ml
do
  echo $file
  file_nat=${file/.ml/.native}
  ocamlbuild -libs nums -I ocaml-lib ${file_nat}
done 

for file in _build/*.native 
do
  echo -e "\n\n\n"
  echo -e "***************************************************"
  echo -e "* Testing ${file}"
  echo -e "***************************************************\n"
  ./$file
done



