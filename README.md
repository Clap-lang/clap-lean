# Clap-lean

Clap-lean is a compiler from a subset of Lean 4 to circuits for SNARK proof-systems.
The compiler is itself written in (Meta) Lean and it is semantics-preserving.

Given a circuit, Clap generates a constraint system that is sound and a witness generator that is complete wrt to it.

## Work in progress

Marco Stronati and Nethermind are currently in the process of finishing the compiler and formally verifying the circuits of [Aptos Keyless](https://alinush.github.io/keyless-zkp) thanks to a grant from the [Aptos foundation](https://aptosfoundation.org/).

[Presentation at ZKProof 8 Rome, May 2026](https://youtu.be/wg3qP3iC_Kg?si=F8Ou4COf2Lgv-XLh&t=148)


## Old work

The [paper](https://arxiv.org/abs/2405.12115) describes an old embedding in Rust and its experimental validation for PlonKish circuits.

This repository is a complete re-design of Clap to take advantage of features of Lean.


## Layout

`Clap/` is the live tree: `Util/` (model-agnostic maths), `Tactic/` (proof automation),
`Model/` (the `ClapM` circuit model and its two back ends), `Lang/` (the gadget library),
then `Poseidon/`, `Keyless/`, `Examples/` and `Test/` on top. `docs/repo-layout.md` has the
layering rule that keeps those apart, and `docs/clap-agent-guide.md` is the entry point for
working on a circuit.

`old/` holds the previous embedding — `F p = ZMod p`, gadgets returning `Option`, and the
`#compile` reifier. It is outside every Lake target and is never built; it is kept as the
reference the port is written against. See `old/README.md`.

## Setup

[Install Elan](https://github.com/leanprover/elan?tab=readme-ov-file#installation):
```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source $HOME/.elan/env
```

Get dependencies from cache and compile:
```
lake exe cache get
lake build
```
