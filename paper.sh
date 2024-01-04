#!/bin/bash
cat paper_*.log | sort -n | uniq > paper.csv
