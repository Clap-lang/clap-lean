# Clap-lean

Clap-lean is a language for writing circuits for SNARK proof-systems with a semantic-preserving and optimizing compiler written in Lean 4.

Given a circuit, Clap generates a constraint system that is sound and a witness generator that is complete wrt to it.

Future work aims to prove functional correctness of the source circuits.

The [paper](https://arxiv.org/abs/2405.12115) describes the approach and its experimental validation in a Rust implementation.

This repository is a complete re-design of Clap to take advantage of features of Lean.
