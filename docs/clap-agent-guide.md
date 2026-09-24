---
name: clap-agent-guide
description: Index and universal rules for working on CLAP circuits in the new model. Read this first, then the task-specific file it routes you to.
when-to-use: Any task that adds, changes, specifies, proves, or ports a CLAP circuit gadget.
---

# CLAP agent guide

You are working in a Lean 4 repository that compiles a subset of Lean to SNARK circuits.
Circuits are built in the `ClapM p` monad ([Clap/Model/](../Clap/Model/)) and their
correctness is stated as a single `ConvertsM` lemma ([Clap/Lang/](../Clap/Lang/)).

Read this file, then go to the one that matches your task. On first contact with CLAP, read
[how-to-clap.md](how-to-clap.md) once before anything else: it is the guided tour of `ClapM`,
`Converts`/`ConvertsM` and `step`, and where it and the other files disagree, it is
authoritative. If you need to know where something lives,
[repo-layout.md](repo-layout.md) has the tree and the rules that keep its layers apart.

## Routing

| Your task | Read | Then |
|---|---|---|
| New to CLAP, or want the why behind `ClapM` / `Converts` / `step` | [how-to-clap.md](how-to-clap.md) | [clap-model.md](clap-model.md) |
| "Where does this file go?", "is this file still alive?", "what may import what?" | [repo-layout.md](repo-layout.md) | — |
| "What is `Converts`?", "how does `ClapM` work?", "where is X defined?" | [clap-model.md](clap-model.md) | — |
| Write a new gadget, or state what an existing one does | [specifying-circuits.md](specifying-circuits.md) — check §Existing inventory before writing anything, and §Iterating gadgets for the `foldlM`/`ofFnM` combinators | [proving-circuits.md](proving-circuits.md) |
| Prove a `convertsM` lemma; a proof is stuck; `step` is misbehaving | [proving-circuits.md](proving-circuits.md) | §Failure modes |
| Move a gadget out of `old/` into the new model | [porting-guide.md](porting-guide.md) | then the two above |
| Give a circuit public inputs; state an end-to-end theorem about a whole program | [public-inputs.md](public-inputs.md) | [clap-model.md](clap-model.md) |

If you are writing a gadget you MUST read both `specifying-circuits.md` and
`proving-circuits.md` before writing Lean. The definition and its proof are designed together;
a gadget written without the proof in mind is usually unprovable without rewriting it.

## Universal rules

These hold for every task. Violating them produces code that does not compile, or proofs that
cannot be closed.

1. **The old model lives in [`old/`](../old/) and is never built.** It is outside every Lake
   target. **NEVER** add an import of anything under `old/` to make something compile, and never
   edit a file there into shape — porting means rewriting into `Clap/Lang/`. See
   [porting-guide.md](porting-guide.md).

   Its model-agnostic maths did survive, and is live under
   [`Clap/Util/`](../Clap/Util/): `BitVec.lean` (`num2bitsLsbPure(V)`, `bits2num(V)` —
   `stepNum2bits` is specified against them), `Wheels.lean`, `Primes.lean`, plus
   `Containers.lean` and `Lemmas.lean`. Import and use those directly; editing them affects the
   live build.

2. **The tree is layered, and imports only ever point downwards.**
   `Util` → `Model` → `Lang/Gate` → `Lang/Core` → `Lang/Data`, with `Poseidon`, `Keyless`,
   `Examples` and `Test` on top. In particular **nothing in `Clap/Model/` may import
   `Clap/Lang/`** — the model is what the gadget library is built on. The single deliberate
   exception is `Clap/Model/Convert/Specialised.lean` importing `Clap/Tactic/Step.lean`, because
   the `step` tactic parses the `Converts` structures defined one file below it.
   [repo-layout.md](repo-layout.md) has the details.

3. **There is no failure effect.** `ClapM p α` cannot reject. Old circuits returned
   `Option`, where `none` meant "unsatisfiable". A `ClapM` action always produces a result and
   always emits its gates. Unsatisfiability is expressed *only* as the `Prop` in the fifth
   argument of `ConvertsM`.

4. **There is no `soundness` or `completeness` theorem, and you must not write one.** Both
   directions live in the single `↔` of `ConvertsM.constraints`. There is deliberately no
   `_spec`, `_sound`, `_complete`, or `_correct` lemma anywhere in `Clap/Lang/` — grep confirms
   it. The aggregate lemma for a gadget named `foo` is `foo.convertsM`, always.

5. **NEVER `unfold` the five eDSL gates.** `eq0`, `share`, `isZero`, `num2bits`, `fpmul` in
   [eDSL.lean](../Clap/Model/eDSL.lean) are `@[irreducible]` on purpose. Reach them through
   their `wellFormed_*`, `eval_edsl_*`, `getResult_*`, `getVarStore_*`, `getCircuit_*` lemmas.
   Unfolding them dumps raw monad plumbing into your goal and the proof will not close.

6. **The back end works; use it.** `Circuit.toCs`
   ([ConstraintSystem/toCs.lean](../Clap/Model/ConstraintSystem/toCs.lean)) and
   `Circuit.toWg` ([WitnessGenerator/toWg.lean](../Clap/Model/WitnessGenerator/toWg.lean))
   both take a `numInputs` and have real branches for all five gates, with per-gate modules
   under `ConstraintSystem/` and `WitnessGenerator/`.
   [Test/Backend.lean](../Clap/Test/Backend.lean) runs a circuit end to end and `#guard`s
   `wellbehaved` / `complete` / `sound`. So a `native_decide` smoke test *is* available — see
   [Poseidon.lean](../Clap/Poseidon/Poseidon.lean), which pins circomlib and `poseidon-ark`
   hash vectors at arities 1–6 that way (by evaluation; Poseidon does not lower yet). The
   `ConvertsM` lemma is still the real evidence; a smoke test is a cheap sanity check on top,
   not a substitute.

7. **`autoImplicit` is off and the unused-variable linter is on**
   ([lakefile.toml](../lakefile.toml)). Bind every implicit explicitly — hence the ubiquitous
   `variable {p : ℕ}` at the top of every file. Lean is `v4.32.0`; Mathlib and CompPoly are
   both pinned to `v4.32.0`.

8. **Verify with `lake build`.** `lake build Clap` builds everything;
   `lake build Clap.Lang.Data.FArray.singleOneArray` builds one gadget and its dependencies.
   `python3 scripts/check-closure.py` then confirms nothing you added is stranded outside the
   build. A gadget is not done until it builds with no `sorry` and no *new* warnings.
   (The baseline is not warning-free: `Clap/Util/Containers.lean:15` emits two
   `linter.dupNamespace` warnings for the `Clap.monads` attribute. Ignore those two; do not add
   more.)

9. **Do not state anything in terms of `CacheExpr`.** It is the heap's internal node type
   ([HashCons/CacheExpr.lean](../Clap/Model/HashCons/CacheExpr.lean)), and there is
   practically never a reason to so much as utter it outside fundamental changes to the
   infrastructure. Gadgets, specs and proofs work with `ExprRef` / `F p` and `Converts`. If a
   statement seems to need `CacheExpr`, restructure the approach. See
   [how-to-clap.md §Clapping](how-to-clap.md#clapping).

## Metavariable conventions

Follow these or your code will read as foreign to the rest of the tree.

| Name | Means |
|---|---|
| `p` | the prime / field modulus |
| `p'` | modulus **limbs** for `fpmul`, never the prime |
| `Γ`, `varStore` | the variable store, `VarStore p` |
| `σ` | the hash-cons heap, `HashConsSt p` — the `ClapM` state holding every hash-consed expression |
| `numAlloc` | the number of allocations so far — the `ClapM` state `StateM ℕ`, and the next free variable index |
| `circuit` | the accumulated gate sequence, `Circuit` — the `ClapM` writer |
| `e!` | a raw `ExprRef` |
| `e` | a bundled `Expr p` (a ref plus the heap it lives in) |
| `x` | a circuit-level reference |
| `x_val` | the ideal (pure Lean) value that `x` represents |
| `h_x` | the `Converts` hypothesis relating `x` to `x_val` |
| `state` | a `ClapMState p` (varStore + σ + numAlloc bundled) |
| `k`, `len`, `w` | vector length, array length, bit width |

## Checklist before you declare a task done

- [ ] `lake build` passes.
- [ ] No `sorry` and no `admit` in what you added. `lake build Clap` has exactly one expected
      `sorry`, `poseidon.convertsM` in
      [Examples/PoseidonProgram.lean](../Clap/Examples/PoseidonProgram.lean) — it is unprovable
      by design, standing in for the `opaque poseidonSpec` in that example. If you see a second
      one, it is yours. (`Clap/Util/Primes.lean` has two more, for the primality of
      `goldilocks` and `bn254`; anything needing primality inherits them.)
- [ ] `native_decide` is allowed as a smoke test, never as the proof of a `convertsM`.
- [ ] The gadget has exactly one aggregate lemma, named `convertsM`, in a namespace matching
      the definition's name. A gadget that needs an input in range but does not range-check it
      also gets `convertsM_unchecked`, with no value-range hypotheses — see
      [specifying-circuits.md](specifying-circuits.md).
- [ ] Its constraints slot is `True` only if the gadget genuinely emits no assertion.
- [ ] The new file is imported from [Clap/Lang/All.lean](../Clap/Lang/All.lean), in
      alphabetical position (case-insensitive order). That is the only index —
      [Clap.lean](../Clap.lean) imports `All.lean` and lists no gadgets itself.
- [ ] It went into the right layer: `Gate/` only for a wrapper around a gate from
      [Model/eDSL.lean](../Clap/Model/eDSL.lean), `Core/` for scalars, booleans, assertions and
      combinators, `Data/` for anything container-shaped. `Core/` must not import `Data/`.
- [ ] You did not touch anything under [`old/`](../old/).
