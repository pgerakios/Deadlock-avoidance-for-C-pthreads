#!/bin/sh

if [ -z "$3" ]; then
    echo "Usage: ./run.sh <times> <nthreads> <nops>"
    exit 1
fi

times=$1
threads=$2
ops=$3

export TIME="user/system/elapsed: %U %S %e"
TIMER="/usr/bin/time --quiet"

# vanilla version

count=0
deadlock=0
sum=0

rm -f OUTPUT.vanilla
touch OUTPUT.vanilla

while [ $sum -lt $times ]; do
    printf "vanilla:\tgood=$count, deadlocks=$deadlock\r"
    if $TIMER ./join $threads $ops >> OUTPUT.vanilla 2>&1; then
        count=$(( $count + 1 ))
    else
        deadlock=$(( $deadlock + 1 ))
    fi
    sum=$(( $count + $deadlock ))
    echo "" >> OUTPUT.vanilla
done

printf "vanilla:\tgood=$count, deadlocks=$deadlock\n"

echo "$times complete runs, $deadlock runs with deadlock." >> OUTPUT.vanilla

# modified version

count=0
deadlock=0
sum=0

rm -f OUTPUT.modified
touch OUTPUT.modified

while [ $sum -lt $times ]; do
    printf "modified:\tgood=$count, deadlocks=$deadlock\r"
    if $TIMER ./join_mod $threads $ops >> OUTPUT.modified 2>&1; then
        count=$(( $count + 1 ))
    else
        deadlock=$(( $deadlock + 1 ))
    fi
    sum=$(( $count + $deadlock ))    
    echo "" >> OUTPUT.modified
done
printf "modified:\tgood=$count, deadlocks=$deadlock\n"

echo "$times complete runs, $deadlock runs with deadlock." >> OUTPUT.modified
