---
name: repo-layout
description: Where everything lives, and the layering rule that imports must respect. Read before adding a file, moving one, or wondering whether something is still alive.
when-to-use: You are adding a new file, cannot find an existing one, or need to know whether a file is part of the build.
---

# Repository layout

Two models coexisted in this tree for a long time. They no longer share a directory: everything
belonging to the old `Option`/`ZMod` embedding is in [`old/`](../old/) and is never built, and
everything under `Clap/` is the live `ClapM` model.

## The live tree

| Directory | Holds | Depends on |
|---|---|---|
| [`Clap/Util/`](../Clap/Util/) | model-agnostic maths and Lean/Std lemmas: `Primes`, `BitVec`, `Wheels`, `Containers`, `Lemmas` | Mathlib/Std only |
| [`Clap/Tactic/`](../Clap/Tactic/) | proof automation — `Step.lean` is the `step` tactic, `Extensions.lean` its environment extension | `Util`, `Model/Convert/Base` |
| [`Clap/Model/`](../Clap/Model/) | the model: hash-consed expression heap, `ClapM`, the `EvalSt` semantics, the `Converts`/`ConvertsM` refinement layer, and both back ends (`ConstraintSystem/`, `WitnessGenerator/`) | `Util`, `Tactic` |
| [`Clap/Lang/`](../Clap/Lang/) | the gadget library — see below | `Util`, `Model` |
| [`Clap/Poseidon/`](../Clap/Poseidon/) | Poseidon as a gadget package of its own, with ~25 000 lines of constant tables under `Constants/` | `Model` |
| [`Clap/Keyless/`](../Clap/Keyless/) | the Aptos Keyless application: `Input.lean` (the input structures and their size constants) and `Allocate.lean` (their public-input allocators) | `Model`, `Lang` |
| [`Clap/Examples/`](../Clap/Examples/) | worked end-to-end programs. `PoseidonProgram.lean` holds the repo's one deliberate `sorry`. | everything |
| [`Clap/Test/`](../Clap/Test/) | executable checks of the back end | `Model` |
| [`R1Serialize/`](../R1Serialize/) | a standalone snarkjs `.r1cs`/`.wtns` writer, its own Lake lib, no `Clap` dependency | nothing |

[`Clap.lean`](../Clap.lean) imports the top of each layer and nothing else. The per-directory
indices are [`Clap/Model/All.lean`](../Clap/Model/All.lean) and
[`Clap/Lang/All.lean`](../Clap/Lang/All.lean) — register new files there, not in `Clap.lean`.

## `Clap/Lang/` in three layers

| Layer | What belongs there |
|---|---|
| `Gate/` | wrappers around a gate from [`Model/eDSL.lean`](../Clap/Model/eDSL.lean): a thin `def` plus its `wellFormed` / `converts` / `constraints` / `convertsM` family. Currently `eq0`, `isZero`, `num2bits`; `share` and `fpmul` are implemented gates still waiting for a wrapper. |
| `Core/` | the language itself — field arithmetic (`F/`), booleans (`FB/`), assertions (`FUnit/`) and the iteration combinators (`Combinators/`). |
| `Data/` | containers — `FArray/`, `FBitVec/`, `FVec/`, `FString/`, `F8/`, and the fixed-width `FBV8`/`F32`/`F64` wrappers in `Widths.lean`. |

`num2bits` is in `Gate/` rather than `Data/FArray/` despite returning an array, because
`Core/F/lessThan.lean` and `Core/FUnit/assert_range.lean` are built on it. That is the whole
reason the three layers are ordered this way.

## The layering rule

**Imports point downwards only:**

```
Util  →  Model  →  Lang/Gate  →  Lang/Core  →  Lang/Data  →  Poseidon, Keyless, Examples, Test
```

In particular:

- **Nothing in `Clap/Model/` may import `Clap/Lang/`.** The model is what the gadget library is
  built on. If a gadget's *type and conversion* are needed by the model — as `PaddedVector` is
  by `PublicInput.lean` — the conversion belongs in `Model/Convert/`, and only the gadgets that
  use it stay in `Lang/Data/`.
- **`Lang/Core/` must not import `Lang/Data/`.**
- **Nothing live may import anything under `old/`.**

There is exactly one deliberate exception: `Model/Convert/Specialised.lean` imports
`Tactic/Step.lean`, because the `step` tactic parses the `Converts`/`ConvertsM` structures
defined in `Model/Convert/Base.lean` one file below it. The real order there is
`Model/Convert/Base` → `Tactic/Step` → `Model/Convert/Specialised`.

## Checking it

```bash
lake build                          # the whole live tree
python3 scripts/check-closure.py    # nothing stranded outside a Lake target
```

`check-closure.py` exits non-zero if a module under `Clap/` or `R1Serialize/` is reachable from
no target. That is the guard against the situation this layout was created to fix: 44 modules
sitting in the tree, imported by nothing, never compiled, and quietly rotting.

## `old/`

See [`old/README.md`](../old/README.md). It is reference source, and it is the specification
for the port — the old `native_decide` corpora say what each gadget was supposed to do.
[`porting-guide.md`](porting-guide.md) is the map.
