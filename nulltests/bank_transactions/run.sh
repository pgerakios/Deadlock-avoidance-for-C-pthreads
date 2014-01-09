#!/bin/sh

if [ "$1" == "" ]; then
    echo "Usage: ./run.sh <times> <max>"
    exit 1
fi

times=$1
max=$2

export TIME="user/system/elapsed: %U %S %e"
TIMER="/usr/bin/time --quiet"

# vanilla version

count=0
deadlock=0

rm -f OUTPUT.vanilla
touch OUTPUT.vanilla

while [ $count -lt $times ]; do
    printf "vanilla:\tgood=$count, deadlocks=$deadlock\r"
    if $TIMER ./boudol $max $max >> OUTPUT.vanilla 2>&1; then
        count=$(( $count + 1 ))
    else
        deadlock=$(( $deadlock + 1 ))
    fi
    echo "" >> OUTPUT.vanilla
done
printf "vanilla:\tgood=$count, deadlocks=$deadlock\n"

echo "$times complete runs, $deadlock runs with deadlock." >> OUTPUT.vanilla

# modified version

count=0
deadlock=0

rm -f OUTPUT.modified
touch OUTPUT.modified

while [ $count -lt $times ]; do
    printf "modified:\tgood=$count, deadlocks=$deadlock\r"
    if $TIMER ./boudol_mod $max $max >> OUTPUT.modified 2>&1; then
        count=$(( $count + 1 ))
    else
        deadlock=$(( $deadlock + 1 ))
    fi
    echo "" >> OUTPUT.modified
done
printf "modified:\tgood=$count, deadlocks=$deadlock\n"

echo "$times complete runs, $deadlock runs with deadlock." >> OUTPUT.modified
