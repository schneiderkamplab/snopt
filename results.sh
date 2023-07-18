#!/bin/bash
echo num_inputs,sn_type,do_max,try_min,try_max,length,saved,num_registers > results/results.csv
cat results/results.txt | grep "^\!" | awk '{print $2","$3","$4","$5","$6","$7","$8","$9;}' >> results/results.csv
