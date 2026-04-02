#!/bin/bash

set -e

if [ -z "$1" ]; then echo "Pass a number of iterations."; fi

for i in $(seq 1 $1); do
  sed -i "s/  -- insert/  bind (eq0 (p:=p) $i) fun () ↦\n  -- insert/" Clap/BenchCircuit.lean
done
