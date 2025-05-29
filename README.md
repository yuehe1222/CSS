# Code for SCCS Algorithm

This repository contains a reference implementation of the algorithms for the paper:
"On Conductance-based Community Search at Billion Scale".


## Experimental Environment
This code can be run on a Linux environment. Our code is compiled on a Linux sever with Intel(R) Xeon(R) Gold 6348 @ 2.60GHz CPU and 256GB RAM running CentOS 7.7.

## Dateset Description
Each network contains two related datasets: "xxx.ungraph.txt.gz" and "xxx.top5000.cmty.txt.gz". We provide the largest connected components in the network and remove real communities with less than 3 nodes.

All public datasets can be downloaded from http://snap.stanford.edu/data/index.html

## Running Format
python3 -u SCCS.py [1. name.ungraph] [2. ground-truth.cmty] 

## Running Instance
python3 -u SCCS.py com-amazon.top5000.cmty.txt com-amazon.ungraph.txt
