# The old model

Everything here belongs to CLAP's **old** embedding: `abbrev F p := ZMod p`, gadgets that
return `Option` (where `none` means "unsatisfiable"), and the `#compile` metaprogram that
reified a Lean definition into a circuit.

**None of it is built.** It is outside every Lake target, it is not on Lean's search path, and
several files here cannot compile at all — `Clap/Poseidon/Run.lean` imports a `Poseidon.lean`
that is entirely commented out, and `Clap/Test/Keyless*.lean` depends on a `Clap/Keyless.lean`
whose 429 lines are 100% comments.

It is kept because it is the **specification** for the port. The old `native_decide` test
corpora say what each gadget was supposed to do, and
[`docs/porting-guide.md`](../docs/porting-guide.md) is the map: which gadget lives where, what
its new-model counterpart is, and what is still outstanding.

## Layout

The tree mirrors the layout these files had when they were live, so every `import Clap.X` line
inside it still reads correctly.

| Path | What it is |
|---|---|
| `Clap/Lang.lean` | the old gadget library (~1100 lines) — *not* the new `Clap/Lang/` directory |
| `Clap/Spec.lean` | the old `Spec.*` decode layer, superseded by `Conversion`/`Converts` |
| `Clap/Compiler/`, `Clap/Circuit.lean`, `Clap/Compilation.lean`, `Clap/Simulation.lean` | the `#compile` reifier and the PHOAS syntax. Retired: `ClapM` builds the circuit by execution, so no reification is needed. |
| `Clap/Cfold.lean`, `Clap/Dedup.lean`, `Clap/Unshare.lean` | circuit-level optimisation passes, subsumed by hash-consing at construction time |
| `Clap/Quadratic.lean`, `Clap/Milestone.lean` | R1CS lowering and the `.r1cs`/`.wtns` driver. These are the only consumers of the still-live `R1Serialize` lib. |
| `Clap/Array.lean`, `Clap/Packing.lean`, `Clap/Base64Len.lean`, `Clap/FString.lean` | gadgets awaiting a port |
| `Clap/Sha2/` | `Basic.lean` and `Cpu.lean` are genuinely model-agnostic (typeclass-parameterised over the word representation) and are reusable as-is; `Circuit.lean` is the old-model instance pack |
| `Clap/JWT.lean`, `Clap/Keyless.lean`, `Clap/HashToField.lean`, `Clap/RSA.lean` | the Aptos Keyless application in the old model |
| `Clap/Test/` | the old test suite, all of it against the `#compile` pipeline |
| `Clap/eDSLState/` | new-model-era files that were superseded: the flat `ConstraintSystem.lean` (an older subset of `ConstraintSystem/`, with `.fpmul => sorry`), `Plan.lean` (a design note, 100% comments), and `IsValid.lean` (a superseded design for what `Conversion`/`Converts` now does) |
| `scripts/`, `runSnarkjs.sh` | fixture generation for `Clap/Test/Keyless*.lean`, and a Groth16 flow over the `.r1cs`/`.wtns` pair only the old path emits |

## Caveat

A few imports here point at files that have since moved in the live tree — for example
`Clap/Circuit.lean` imports `Clap.eDSLState.Wheels`, which is now `Clap.Util.Containers`.
Nothing is compiled, so nothing breaks, but do not expect an old file to build by dropping it
back into `Clap/`.

## Rules

- Never add an import of anything under `old/` to a live file.
- Never edit a file here into shape. Porting means **rewriting into `Clap/Lang/`** — see
  [`docs/porting-guide.md`](../docs/porting-guide.md).
