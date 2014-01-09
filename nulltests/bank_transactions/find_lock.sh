#!/bin/sh

while [ 1 ]; do
  ./boudol_mod 10000 10000 > /dev/null || break
done
