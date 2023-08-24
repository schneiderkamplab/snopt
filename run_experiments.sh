#!/bin/bash
for i in $(seq $1 $2)
do
  ./experiments.sh $i $i | tee -a experiments.log &
done
