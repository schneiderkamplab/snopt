#!/bin/bash
time python generate.py -v --progress -d generated \
 -f $1 -t $2 \
 -r True -r False \
 --fallback False --fallback True \
 -b sat -b z3 \
 --prune False --prune True \
 --do-max False --do-max True \
 --try-min False --try-min True \
 --try-max False --try-max True \
 --slice -1 --slice 0 --slice 1 --slice 2 --slice 4 \
 