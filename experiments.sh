#!/bin/bash
time python generate.py -f $1 -t $2 -v --progress --do-max False --do-max True --try-min False --try-min True --try-max False --try-max True --prune False --prune True --slice -1 --slice 0 --slice 1 --slice 2 --slice 4 -r True -r False --fallback False --fallback True -b sat -b z3 -d generated
