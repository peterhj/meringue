#!/bin/sh
theory_file="data/geometry.txt"
problem_file="data/reduced_imo_2009_p2_v2.txt"
if [ -z "$1" ]; then
  ./target/release/run_oneshot "${theory_file}" "${problem_file}"
else
  ./target/release/run_oneshot "${theory_file}" "${problem_file}" "$1"
fi
