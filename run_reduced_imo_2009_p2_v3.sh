#!/bin/sh
theory_file="data/geometry.txt"
problem_file="data/reduced_imo_2009_p2_v3.txt"
# NB: default_seed=2 is a known good seed (100 steps to solve);
# another seed is 101 (130 steps).
if [ -z "$1" ]; then
  default_seed="2"
  ./target/release/run_oneshot "${theory_file}" "${problem_file}" "${default_seed}"
else
  ./target/release/run_oneshot "${theory_file}" "${problem_file}" "$1"
fi
