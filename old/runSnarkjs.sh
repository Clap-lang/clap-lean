#!/bin/bash

set -e

name="$1"

snarkjs wtns check "$name".r1cs "$name".wtns || exit 1

# from https://docs.circom.io/getting-started/proving-circuits/

if [ ! -f "final.ptau" ]; then
  snarkjs powersoftau new bn128 12 pot12_0000.ptau
  snarkjs powersoftau contribute pot12_0000.ptau pot12_0001.ptau --name="First contribution" << EOF
random
EOF
  snarkjs powersoftau prepare phase2 pot12_0001.ptau final.ptau
  rm pot12_0000.ptau pot12_0001.ptau
fi

snarkjs groth16 setup "$name.r1cs" final.ptau "$name"_0000.zkey

snarkjs zkey contribute "$name"_0000.zkey "$name".zkey --name="1st Contributor Name" << EOF
random
EOF

rm "$name"_0000.zkey

snarkjs groth16 prove "$name".zkey "$name.wtns" proof.json public.json

snarkjs zkey export verificationkey "$name".zkey vkey.json

snarkjs groth16 verify vkey.json public.json proof.json
