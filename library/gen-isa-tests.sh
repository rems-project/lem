#!/bin/sh -e

dir=$1
cd $dir
outfile=LemTests.thy

echo -e "theory LemTests\n" > $outfile
echo -e "\n\nimports Main\n" >> $outfile

for file in *Auxiliary.thy
do
  file_thy=${file%.thy}
  echo -e "\t\"$file_thy\"" >> $outfile
done 

echo -e "\n\nbegin\nend\n" >> $outfile
