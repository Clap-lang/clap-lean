#!/bin/bash

set -e

echo -n "open "
for file in "$@"; do
  defs=$(sed -nE 's/^namespace +([a-zA-Z0-9_.]+).*/\1/p' "$file")
  echo "$defs"
done | tr '\n' ' '

echo
for file in "$@"; do
  defs=$(sed -nE 's/^(private |protected |noncomputable |unsafe |partial )*(def|abbrev) +([a-zA-Z0-9_.]+).*/\3/p' "$file")
  modules=$(echo $file | sed 's/[.].*/./' | tr '/' '.')
  for def in $defs; do echo "$def"; done
done | tr '\n' ' '
echo

echo "There were nested in a where"
for file in "$@"; do
  def=$(rg where -B 10 $file | sed -nE 's/^(private |protected |noncomputable |unsafe |partial )*def +([a-zA-Z0-9_.]+).*/\2/p')
  inners=$(rg where -A 10 $file | sed -nE 's/^  ([a-zA-Z0-9]+).*/\1/p')
  for i in $inners; do
    echo $def.$i
  done
done | tr '\n' ' '
echo
