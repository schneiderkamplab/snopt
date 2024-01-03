#!/bin/bash
for prune in False True
do
  for realloc in False True
  do
    for slice in -1 0 1 2 4
    do
      for domax in False True
      do
        for trymin in False True
        do
          for trymax in False True
          do
            for backend in sat z3
            do
              time python generate.py -v --progress -d generated \
 -f $1 -t $2 \
 -r $realloc \
 --fallback False --fallback True \
 -b $backend \
 --prune $prune \
 --do-max $domax \
 --try-min $trymin \
 --try-max $trymax \
 --slice $slice \
 &
            done
          done
        done
      done
    done
  done
done
wait
