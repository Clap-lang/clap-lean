---
name: clap-agent-guide
description: Index and universal rules for working on CLAP circuits in the eDSLState model. Read this first, then the task-specific file it routes you to.
when-to-use: Any task that adds, changes, specifies, proves, or ports a CLAP circuit gadget.
---

# CLAP agent guide

You are working in a Lean 4 repository that compiles a subset of Lean to SNARK circuits.
Circuits are built in the `ClapM p` monad ([Clap/eDSLState/](../Clap/eDSLState/)) and their
correctness is stated as a single `ConvertsM` lemma ([Clap/Lang/](../Clap/Lang/)).

Read this file, then go to the one that matches your task.

## Routing

| Your task | Read | Then |
|---|---|---|
| "What is `Converts`?", "how does `ClapM` work?", "where is X defined?" | [clap-model.md](clap-model.md) | — |
| Write a new gadget, or state what an existing one does | [specifying-circuits.md](specifying-circuits.md) | [proving-circuits.md](proving-circuits.md) |
| Prove a `convertsM` lemma; a proof is stuck; `step` is misbehaving | [proving-circuits.md](proving-circuits.md) | §Failure modes |
| Move a gadget from `Clap/Array.lean`, `Clap/Lang.lean`, `Sha2`, `JWT`, … into the new model | [porting-guide.md](porting-guide.md) | then the two above |

If you are writing a gadget you MUST read both `specifying-circuits.md` and
`proving-circuits.md` before writing Lean. The definition and its proof are designed together;
a gadget written without the proof in mind is usually unprovable without rewriting it.

## Universal rules

These hold for every task. Violating them produces code that does not compile, or proofs that
cannot be closed.

1. **Only two trees are live.** [Clap.lean](../Clap.lean) imports `Clap/eDSLState/*` and
   `Clap/Lang/*` and nothing else. Everything from line 40 onwards sits inside a comment block
   headed *"Goodbye, sweet prince."* — `Clap/Array.lean`, `Clap/Lang.lean`, `Clap/Spec.lean`,
   `Sha2`, `JWT`, `RSA`, `Poseidon`, the `Compiler/` metaprogram, all of it. **NEVER** add an
   import of an old file to make something compile.

2. **`Clap/Lang.lean` is not `Clap/Lang/`.** The *file* `Clap/Lang.lean` (~1100 lines) is the
   OLD `Option`/`ZMod`-valued model. The *directory* `Clap/Lang/` is the new gadget library.
   They share a name and nothing else. Never copy style, definitions, or lemma shapes from the
   file into the directory.

3. **There is no failure effect.** `ClapM p α` cannot reject. Old circuits returned
   `Option`, where `none` meant "unsatisfiable". A `ClapM` action always produces a result and
   always emits its gates. Unsatisfiability is expressed *only* as the `Prop` in the fifth
   argument of `ConvertsM`.

4. **There is no `soundness` or `completeness` theorem, and you must not write one.** Both
   directions live in the single `↔` of `ConvertsM.constraints`. There is deliberately no
   `_spec`, `_sound`, `_complete`, or `_correct` lemma anywhere in `Clap/Lang/` — grep confirms
   it. The aggregate lemma for a gadget named `foo` is `foo.convertsM`, always.

5. **NEVER `unfold` the five eDSL gates.** `eq0`, `share`, `isZero`, `num2bits`, `fpmul` in
   [eDSL.lean](../Clap/eDSLState/eDSL.lean) are `@[irreducible]` on purpose. Reach them through
   their `wellFormed_*`, `eval_edsl_*`, `getResult_*`, `getVarStore_*`, `getCircuit_*` lemmas.
   Unfolding them dumps raw monad plumbing into your goal and the proof will not close.

6. **NEVER build on `IsValid` or `VarStoreSize`.** [IsValid.lean](../Clap/eDSLState/IsValid.lean)
   compiles but is referenced nowhere. It is a superseded design for what `Conversion` /
   `Converts` now does.

7. **Do not assume the back end works.** `ConstraintSystem.lean`, `WitnessGenerator.lean`,
   `Plan.lean` and `Test.lean` are commented out of `Clap.lean`; two of them do not even parse.
   `Circuit.toCs`'s `.fpmul` branch is `sorry`. There is no working executable path from a
   `ClapM` action to a satisfying witness, so there is **no `native_decide` smoke test
   available** for a new gadget. The `ConvertsM` lemma is the only evidence a gadget works.

8. **`autoImplicit` is off and the unused-variable linter is on**
   ([lakefile.toml](../lakefile.toml)). Bind every implicit explicitly — hence the ubiquitous
   `variable {p : ℕ}` at the top of every file. Lean is `v4.32.0`, Mathlib is pinned to
   `v4.32.0`.

9. **Verify with `lake build`.** There is no test suite for the new model. `lake build Clap`
   builds everything; `lake build Clap.Lang.FArray.singleOneArray` builds one gadget and its
   dependencies. A gadget is not done until it builds with no `sorry` and no *new* warnings.
   (The baseline is not warning-free: `Clap/eDSLState/Wheels.lean:15` emits two
   `linter.dupNamespace` warnings for the `Clap.monads` attribute. Ignore those two; do not add
   more.)

## Metavariable conventions

Follow these or your code will read as foreign to the rest of the tree.

| Name | Means |
|---|---|
| `p` | the prime / field modulus |
| `p'` | modulus **limbs** for `fpmul`, never the prime |
| `Γ`, `varStore` | the variable store, `VarStore p` |
| `σ` | the hash-cons heap, `HashConsSt p` |
| `e!` | a raw `ExprRef` |
| `e` | a bundled `Expr p` (a ref plus the heap it lives in) |
| `x` | a circuit-level reference |
| `x_val` | the ideal (pure Lean) value that `x` represents |
| `h_x` | the `Converts` hypothesis relating `x` to `x_val` |
| `state` | a `ClapMState p` (varStore + σ + numAlloc bundled) |
| `k`, `len`, `w` | vector length, array length, bit width |

## Checklist before you declare a task done

- [ ] `lake build` passes.
- [ ] No `sorry`, no `admit`, no `native_decide` in what you added.
- [ ] The gadget has exactly one aggregate lemma, named `convertsM`, in a namespace matching
      the definition's name.
- [ ] Its constraints slot is `True` only if the gadget genuinely emits no assertion.
- [ ] The new file is imported from [Clap/Lang/All.lean](../Clap/Lang/All.lean) **and**
      [Clap.lean](../Clap.lean), in alphabetical position in both.
- [ ] You did not touch any file behind the "Goodbye, sweet prince" comment.
