#! /bin/sh

mkdir callgrind
rm callgrind/callgrind.out.*
valgrind --tool=callgrind --separate-threads=yes ./$@ > /dev/null
mv callgrind.out.* callgrind/

file=$1
dir=`dirname $1`

for f in `ls $dir/callgrind/callgrind.out*`; do
  callgrind_annotate $f
done
