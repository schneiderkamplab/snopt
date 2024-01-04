#!/bin/bash
for i in $(seq $1 $2)
do
  time python generate.py -v --progress -d generated \
 -f $i -t $i \
 -r True \
 --fallback False \
 -b z3 \
 --prune True \
 --do-max False \
 --try-min True \
 --try-max False \
 --slice -1 \
 -s jgamble_best -s batcher \
 &
done
wait
