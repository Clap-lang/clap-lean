---
name: proving-circuits
description: Rules for proving a CLAP gadget's ConvertsM lemma - the step tactic, the three proof skeletons, the induction recipe, and failure modes.
when-to-use: You are proving a convertsM lemma, or a CLAP proof is stuck.
---

# Proving CLAP circuits

Read [clap-agent-guide.md](clap-agent-guide.md) first, and
[specifying-circuits.md](specifying-circuits.md) for the shape of the statement you are proving.

## What you actually have to show

`ConvertsM` is a three-field structure ([Convert/Base.lean](../Clap/Model/Convert/Base.lean)):

| Field | Obligation | Usually closed by |
|---|---|---|
| `result` | the returned refs evaluate to the ideal value | `step` chaining, then `converts_of_converts` / an explicit `Converts` lemma |
| `wellFormed` | the action's gates and counters are well-formed | `grind`, seeded with a `wellFormed_*` lemma from `eDSL.lean` |
| `constraints` | the emitted constraints `↔` your stated condition | `grind [ClapM.runAndEval]` when `True`; real work otherwise |

You almost never prove these by hand for a composite gadget. You chain sub-gadget `convertsM`
lemmas with `step`, and the three fields come along for free.

## Pick your skeleton

```
Does the gadget body end in `return` / `pure`?
├── yes → Skeleton 2   (unfold → steps → apply convertsM_pure)
└── no
    ├── it is a composition of existing gadgets → Skeleton 1
    │      (unfold → steps → apply convertsM_of_convertsM)
    └── it is a raw gate or HashConsM primitive → Skeleton 3
           (constructor / where-clause, three field lemmas)

Does the body iterate (mapM / foldlM)?  → additionally the induction recipe below.

Can two or more steps each fail (non-`True` constraints)?
  → `step` will not do it; apply `convertsM_bind_and` by hand. See below.
```

## The `step` tactic

Defined at [Clap/Tactic/Step.lean:199](../Clap/Tactic/Step.lean#L199) (`step`) and [:214](../Clap/Tactic/Step.lean#L214) (`step_state`), over `step_impl` at [:160](../Clap/Tactic/Step.lean#L160). This is
the whole proof engine and it is not documented anywhere else.

```
step <ConvertsM term> as <name>
```

What it does, in order:

1. Reads the goal, which **must** be `Clap.ConvertsM …`. Looks at the head of the `action`:
   `Bind.bind` → applies `convertsM_bind`; `Functor.map` → applies `convertsM_map`; anything
   else → warns *"Conclusion unchanged; spec missing for: …"* and does not restructure.
2. Applies your supplied `ConvertsM` term to discharge the head subgoal. If it does not unify
   exactly you get *"Failed to unify. Bad."*.
3. **Reframes every existing `Converts` hypothesis through the new state** using
   `converts_skip`, clearing the old ones and re-asserting them under the same user names. This
   is why `h_idx`, `h_a` and friends stay usable after several `step`s.
4. Introduces three hypotheses: `h_<name>` (the `.result`, i.e. a `Converts` fact about this
   step's output), `h_wellFormed`, `h_constraints`.
5. `set`s three abbreviations: `<name>` for the action, `<name>_result` for
   `<name>.getResult state.numAlloc state.σ`, `<name>_state` for `<name>.getState state`.
6. Runs `all_goals constraints`, where `constraints` is `first | (intros; trivial) | skip`.

Consequences worth internalising:

- The hypothesis introduced by `step … as foo` is **`h_foo`**. That is the name you pass to the
  next step.
- For a `True`-constraint chain, step 6 discharges the `convertsM_bind` side goals silently and
  you see nothing. For a real-constraint chain it cannot, and the two implication goals of
  `convertsM_bind` survive to the end of the proof. That is where soundness and completeness
  show up — see below.
- **`step` goes through `convertsM_bind`, so it cannot sequence two assertions.** At most one
  step in the chain may have a non-`True` constraint, and it must be the last. See
  [When `step` does not apply](#when-step-does-not-apply--two-or-more-assertions).
- `step` takes an arbitrary term, not just a library lemma. Feeding it an induction hypothesis
  is idiomatic: `step @h_k fvals_base vals_base this as mapM` in
  [FArray/sum.lean](../Clap/Lang/Data/FArray/sum.lean), and `step h_len as mapM` in
  [FArray/OneHotRaw.lean](../Clap/Lang/Data/FArray/OneHotRaw.lean).

### `step_state`

```
step_state <ConvertsM term> as <name>
```

Identical, but skips stages 1–2 (the goal-shape analysis and the `convertsM_bind` application).
Use it when the goal's head is neither `bind` nor `map` and you have already restructured by
hand. No current gadget needs it.

### Before you can `step`

`step` matches only on a `Bind.bind` or `Functor.map` head, so normalise first:

| Situation | Do |
|---|---|
| Always, first line | `unfold <name>` |
| The body uses `+`, `-`, `*` on `F p` and `step` will not match | `rw [add_def]` / `rw [sub_def]` / `rw [mul_def]` |
| The body should be read as its generalised helper | `simp [←<helper>.eq_def]` |
| The body is a `mapM`/`foldlM` | rewrite with the `_succ` equation first |

`sub_def` in [FB/eq.lean](../Clap/Lang/Core/FB/eq.lean) and `simp [←sum'.eq_def]` in
[FArray/sum.lean](../Clap/Lang/Data/FArray/sum.lean) are the worked cases.

**Whichever spelling the definition used, the proof names `mk*`.** `Clap.Lang.mkAdd`/`mkSub`/
`mkMul` are *defined as* `+`/`-`/`*` ([F/mkAdd.lean:9-10](../Clap/Lang/Core/F/mkAdd.lean#L9-L10)), so
a body written with operators is stepped with `mkAdd.convertsM` / `mkSub.convertsM` /
`mkMul.convertsM` exactly as before. There is no `add.convertsM`.

Whether you also need the `*_def` rewrite depends on where the operator sits:

- **No rewrite** when each operator is the action of its own bind, i.e. `let x ← a - b`. `step`'s
  `lemmaOfNextCommand` sees `Bind.bind` as the head and matches directly —
  [F/conditionalSwap.lean:31-35](../Clap/Lang/Core/F/conditionalSwap.lean#L31-L35) steps three times
  with no normalisation at all.
- **Rewrite first** when the operator is buried in a continuation, as in `isZero (←(a - b))` —
  [FB/eq.lean:26](../Clap/Lang/Core/FB/eq.lean#L26) needs its `rw [sub_def]`.

When in doubt, try `step` first; if it reports no match, add the rewrite.

### When `step` does not apply — two or more assertions

`step` applies `convertsM_bind`, whose continuation obligation is
`ConvertsM … (constraints1 → constraints)`. Because `ConvertsM`'s third field is an `↔` with the
constraints the continuation *actually* emits, that slot is pinned to its true constraint `C₂`.
So `convertsM_bind` demands

```
C₂  ↔  (C₁ → constraints)
```

and when `C₁` can fail there is no `constraints` that satisfies it. For `do eq0 a; eq0 b` with
the intended spec `a_val = 0 ∧ b_val = 0` the goal reduces to

```
b_val = 0  ↔  (a_val = 0 → a_val = 0 ∧ b_val = 0)
```

false whenever `a_val ≠ 0` and `b_val ≠ 0`. **This is not a proof you are getting wrong. The
statement is unprovable in that shape.**

So the rule is: in a `step` chain **at most one action may have a non-`True` constraint, and it
must be the last one.** Every gadget written before this was documented happens to satisfy that
— `assertBool` is three `True` steps then one `eq0`, `singleOneArray` is three `True` steps then
one `assert_eq` — which is why it never surfaced.

As soon as two steps can each fail, drop `step` for that bind and apply
[`convertsM_bind_and`](../Clap/Model/Convert/Base.lean) by hand:

```lean
lemma convertsM_bind_and
  (h_action   : ConvertsM conversion1 action state action_val constraints1)
  (h_function : ConvertsM conversion2 (function (action.getResult state.numAlloc state.σ))
                          (action.getState state) function_val constraints2)
  : ConvertsM conversion2 (action >>= function) state function_val (constraints1 ∧ constraints2)
```

It takes each half at its own honest constraint and conjoins them, which is what
`Circuit.runAndEval_bind_constraints` says the semantics does anyway. Then reshape the
conjunction into the spec you want with `convertsM_of_convertsM`.

Two consequences for the hand-rolled version, both easy to trip on:

- `step` was also doing the state reframing for you (stage 3). Applying `convertsM_bind_and`
  directly means you must carry hypotheses forward yourself with `converts_skip`, and reach the
  accumulator's post-state fact as `h_action.result`.
- `step` was `set`ting `<name>_state`. Without it you write `action.getState state` out, or
  bind it with a `have` first.

The worked case is `convertsM_foldlM_constraints` in
[Combinators/foldlM.lean](../Clap/Lang/Core/Combinators/foldlM.lean) — a fold whose every element
asserts, so every iteration is a two-assertion bind:

```lean
    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih (h_f h_ih.result (converts_skip h_ih h_last)))
    . conv_rhs => rewrite [h_vals]
      simp
    . constructor
      . rintro ⟨h_prefix, h_elem⟩ ⟨i, h_i⟩     -- (∀ i < k, P) ∧ P k  →  ∀ i < k+1, P
        …
```

Its sibling `convertsM_foldlM` (step constraint `True`) could have used `step`; it uses
`convertsM_bind_and` too, purely so the two proofs stay the same shape.

## Skeleton 1 — straight-line composition

`unfold` → one `step` per bind → close the tail call with `convertsM_of_convertsM`.

From [FB/eq.lean](../Clap/Lang/Core/FB/eq.lean), complete:

```lean
lemma convertsM
  [p.AtLeastTwo] {state} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
: ConvertsM FB.conversion (eq a b) state (a_val == b_val) True
:= by
  unfold eq
  rw [sub_def]

  step mkSub.convertsM h_a h_b as sub
  apply convertsM_of_convertsM (isZero.convertsM h_sub)
  . grind      -- val1 = val2
  . grind      -- constraints1 ↔ constraints2
```

[F/conditionalSwap.lean](../Clap/Lang/Core/F/conditionalSwap.lean) is the same skeleton one step
longer, and shows the operator spelling in the definition with no `*_def` rewrite needed:

```lean
def conditionalSwap (sel : FB p) (a b : F p) : ClapM p (F p) := do
  let diff ← a - b
  let scaled ← diff * sel
  mkAdd scaled b

-- …
  unfold conditionalSwap
  have h_sel_f := F.converts_of_FB_converts h_sel
  step mkSub.convertsM h_a h_b as diff
  step mkMul.convertsM h_diff h_sel_f as scaled
  apply convertsM_of_convertsM (mkAdd.convertsM h_scaled h_b)
  . cases sel_val <;> simp
  . trivial
```

`convertsM_of_convertsM h h_val h_constraints` leaves exactly two goals: the value equality and
the constraints bi-implication. Close them with `rfl`, `grind`, `simp` or `trivial`.

When a step changes the conversion (`F` ↔ `FB`), do the cast with a `have` before applying —
[FB/not.lean](../Clap/Lang/Core/FB/not.lean):

```lean
  unfold not
  step mkF.convertsM as one
  have h_a_f := F.converts_of_FB_converts h_a
  have h_sub := FB.convertsM_of_F_convertsM (mkSub.convertsM h_one h_a_f)
  apply convertsM_of_convertsM (h_sub _)
  . grind
  . trivial
  . cases a_val <;> simp     -- the `_` above: convertsM_of_F_convertsM's `val.val < 2`
```

## Skeleton 2 — body ends in `return`

Same, but finish with `convertsM_pure`. From
[FArray/singleOneArray.lean](../Clap/Lang/Data/FArray/singleOneArray.lean):

```lean
  unfold singleOneArray

  step oneHotRaw.convertsM h_idx h_len as oneHot
  step FArray.sum.convertsM h_oneHot as sum
  step mkF.convertsM as one
  step assert_eq.convertsM h_sum h_one as assert_eq
  apply convertsM_pure
  . exact h_oneHot     -- the returned value converts
  . <soundness>
  . <completeness>
```

## Skeleton 3 — a primitive from scratch

`constructor` (or a `where` clause) and discharge the three fields separately.

From [F/mkAdd.lean](../Clap/Lang/Core/F/mkAdd.lean), whose body is now just `def mkAdd (a b : F p) :
ClapM p (F p) := a + b` — so `unfold mkAdd` exposes the operator, which is by `rfl` the
`liftM (HashConsM.mkAdd a b)` the instance produces, not a `saveExpr` call:

```lean
  unfold mkAdd
  constructor
  · exact hashConsM_converts h_a h_b
  . grind
  . grind [ClapM.runAndEval]
```

The `Converts` half is factored into its own lemma, stated directly on the operator form
(`ClapM.getState (a + b) state` and `ClapM.getResult (a + b) state.numAlloc state.σ`) and proved
by destructuring both inputs:

```lean
  simp [ClapM.getState]
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_length, b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . grind
```

For a gate-emitting primitive, use the `where`-clause form and the `wellFormed_*` lemma from
`eDSL.lean` — [FUnit/eq0.lean](../Clap/Lang/Gate/eq0.lean) is the template. The `wellFormed`
lemma is always the same three bullets:

```lean
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_eq0
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind
```

## The two `↔` directions — the hard part

For any gadget whose constraints slot is not `True`, `step` cannot discharge the
`convertsM_bind` implications, and they arrive as extra goals after `convertsM_pure`. They are
soundness and completeness, and they are where the real mathematics lives.

`singleOneArray`'s pair, in full:

```lean
  . simp                              -- SOUNDNESS: emitted constraint ⟹ idx_val.val < len
    intro h_sum
    by_contra h_idx_val
    rewrite [Vector.sum_ofFn_eq_zero_of_eq_zero] at h_sum
    . simp at h_sum
    . grind
  . simp                              -- COMPLETENESS: idx_val.val < len ⟹ emitted constraint
    intro h_idx_val
    clear *-h_len h_idx_val
    induction' len with len ih
    . grind
    . specialize ih (by grind)
      rewrite [Vector.ofFn_succ]
      by_cases h : idx_val.val = len
      …
```

Soundness here is "if the index were out of range every bit would be 0, so the sum would be 0,
not 1" — a `by_contra` plus a helper lemma. Completeness is "the sum of a one-hot vector with
the hot bit in range is 1" — induction on `len`. Neither is automatable. Budget for them.

Note the helper `Vector.sum_ofFn_eq_zero_of_eq_zero` is proved *in the gadget's own namespace*,
immediately above `convertsM`. That is the right place for one-off arithmetic lemmas.

## Induction recipe for iterating gadgets

Two worked strategies, both in the tree.

### Strategy A — stay in `Vector`, induct on the length

[FArray/sum.lean](../Clap/Lang/Data/FArray/sum.lean). The trick is reassociating the vector so the
fold exposes its last step:

```lean
  induction' k with k h_k
  . -- base: rewrite the fold to `pure init`, then `apply convertsM_pure`
    apply convertsM_pure <;> [skip; exact True.intro]
  . have := FArray.converts_vector_cast (k2 := k) (FArray.converts_pop h_vals) (by trivial)
    set fvals_base := Vector.cast (m := k) (by trivial) f_vals.pop
    set vals_base  := Vector.cast (m := k) (by trivial) vals.pop

    have h_push : f_vals = fvals_base.push f_vals[k] := by
      ext; rewrite [Vector.getElem_push]; split
      . simp [fvals_base]
      . grind
    rewrite [h_push]
    simp [Vector.foldlM_push]

    step @h_k fvals_base vals_base this as mapM      -- the IH, fed to `step`

    have h_fvals_k := F.converts_of_FB_converts (FArray.converts_getElem h_vals (Nat.lt_succ_self k))
    apply convertsM_of_convertsM (mkAdd.convertsM h_mapM h_fvals_k)
    …
```

Ingredients: `FArray.converts_pop`, `converts_vector_cast`, `converts_getElem`, `Vector.foldlM_push`,
and the `h_push : v = v.pop.push v[k]` rewrite proved by `ext; rewrite [Vector.getElem_push]; split`.

### Strategy B — drop to `FList`, induct on a reversed list

[FArray/OneHotRaw.lean](../Clap/Lang/Data/FArray/OneHotRaw.lean). Usually easier: `List` has more
Mathlib support and no length index to fight.

```lean
  apply FArray.convertsM_of_convertsM_toList     -- turn the FArray goal into an FList goal
  simp_rw [toList_map_oneHotRaw_eq_oneHotRaw']
  unfold oneHotRaw' oneHotRaw'_aux
  simp [Vector.toList_ofFn, List.ofFn_eq_map, List.finRange_eq_pmap_range,
        List.map_pmap, List.range_eq_range']

  set list := List.range' 0 len
  have not_this : ∀ x ∈ list, x < p := by grind
  clear_value list

  rw [←list.reverse_reverse] at not_this ⊢       -- induct from the right end
  set list := list.reverse
  clear_value list
  induction' eq_ih : list.length with len h_len generalizing list
  . aesop
  . rcases list with _ | ⟨hd, tl⟩
    · grind
    · simp
      specialize h_len tl (by aesop (add safe (by grind))) (by grind)
      simp at h_len

      step h_len as mapM
      step mkF.convertsM as mkHd
      step eq.convertsM h_idx h_mkHd as eq

      apply FList.converts_append h_mapM
      apply FList.converts_singleton_of_converts_FB
      apply converts_of_converts h_eq
      …
```

### Context-management moves you will need

These are non-obvious and both proofs depend on them:

| Move | Why |
|---|---|
| `set x := …` then `clear_value x` | abstract a term so induction does not unfold it |
| `clear *-h_len h_idx_val` | prune the context before an induction, or the IH is unusable |
| `induction' eq : l.length with … generalizing l` | induct on a length while generalising the list |
| `rw [←list.reverse_reverse]` | induct from the right end of a list |
| `specialize ih (by grind)` | discharge the IH's side condition inline |
| `convert ih` then `grind` | close a goal that differs from the IH only up to arithmetic |

## Type-changing moves — do not re-derive these

| Lemma | Does |
|---|---|
| `F.converts_of_FB_converts` | `FB` fact → `F` fact, value becomes `if b then 1 else 0` |
| `FB.converts_of_F_converts` | `F` fact + `val.val < 2` → `FB` fact (needs `[p.AtLeastTwo]`) |
| `FB.convertsM_of_F_convertsM` | the same at action level |
| `converts_cast` | change conversion when `toExprs` and `conversion` agree |
| `converts_of_converts` | rewrite the ideal value of a `Converts` |
| `convertsM_of_convertsM` | rewrite value **and** constraints of a `ConvertsM` |
| `converts_skip` | carry a `Converts` past an intervening action (what `step` uses) |
| `convertsM_bind_and` | sequence two actions that **both** assert; `step`/`convertsM_bind` cannot |
| `FArray.converts_iff_FB_converts` | pointwise view of an `FArray` fact |
| `FArray.converts_push` / `converts_pop` / `converts_getElem` / `converts_vector_cast` | vector surgery |
| `FArray.convertsM_of_convertsM_toList` | turn an `FArray` goal into an `FList` goal |
| `FList.converts_append` / `converts_singleton_of_converts_FB` / `converts_of_converts_FB` | list assembly |
| `FUnit.converts` | always true |

## Automation

`grind` is the default finisher; most model lemmas already carry `@[grind =]` / `@[grind .]`.
Seeds that appear in real proofs:

```
grind [ClapM.runAndEval]            -- the `constraints` field of a no-op gadget
grind [ClapM.getState]              -- state bookkeeping
grind [Converts]  /  grind [cases Converts]
grind [=Expr.varSet_wellFormed]     -- the varSet_wf field
grind [=Expr.varSet, =Expr.varSet_wellFormed]
grind [=isZero, ClapM.getState]
simp [Clap.monads]                  -- blast through monad plumbing
aesop (add safe (by grind))
```

When you annotate a new lemma, pick the right `grind` variant: `=` forward rewrite, `_=_`
bidirectional, `→` / `←` implication, `.` use-as-fact, `! .` aggressive, `cases` case-split,
`norm` normalisation, `ext` extensionality.

## Failure modes

| Symptom | Cause | Fix |
|---|---|---|
| *"Conclusion unchanged; spec missing for: …"* | the action's head is not `bind`/`map` | `unfold` first; or `rw [add_def/sub_def/mul_def]` if an operator is buried in a continuation (see [Before you can step](#before-you-can-step)); or use `step_state` |
| No `.convertsM` lemma seems to exist for the `+`/`-`/`*` in the body | you are looking for the wrong name | the operators *are* `mkAdd`/`mkSub`/`mkMul`; step with `mkAdd.convertsM` etc. |
| *"Failed to unify. Bad."* | the supplied `ConvertsM` does not match the head of the bind | check the conversion (`F` vs `FB`), and whether you need a cast lemma first |
| *"Assumptions of shape `Converts` refer to multiple states"* | a hypothesis was not carried forward | it should have been reframed by `step`; if you introduced it manually, apply `converts_skip` yourself |
| *"Expected ConvertsM. Got: …"* | you passed a `Converts`, not a `ConvertsM`, to `step` | use `step` with the `.convertsM` lemma; a bare `Converts` is a `have`, not a step |
| Goal explodes into raw `WriterT`/`StateT` terms | you unfolded an `@[irreducible]` gate | undo; go through `getResult_*` / `getCircuit_*` / `wellFormed_*` instead |
| The constraints `↔` will not close and looks false | your slot-5 condition is wrong (often spuriously `True`) | fix the specification, not the proof |
| The constraints `↔` reads `C₂ ↔ (C₁ → … C₁ … ∧ C₂)` and is false when `C₁` fails | you used `step`/`convertsM_bind` across **two** assertions; the shape is unprovable, not merely hard | re-do that bind with `convertsM_bind_and`, then reshape with `convertsM_of_convertsM`. See [When `step` does not apply](#when-step-does-not-apply--two-or-more-assertions) |
| An extra unexplained goal at the end of a Skeleton-2 proof | the `convertsM_bind` implications for a non-`True` constraint | that is soundness/completeness; prove them |
| The constraints goal reads `… ↔ (True → True → … → P)` and `constructor`/`intro` then mismatches | each preceding `True`-constraint step contributes one `True →` via `convertsM_bind` | a bare `simp` absorbs them, but a targeted script must strip them first: `simp only [true_implies]`. See [FB/assertBool.lean](../Clap/Lang/Core/FB/assertBool.lean) |

## Verification

```
lake build Clap                          # everything
lake build Clap.Lang.FArray.sum          # one gadget and its dependencies
```

Lean `v4.32.0`, Mathlib and CompPoly both pinned to `v4.32.0`, `autoImplicit false`,
`linter.unusedVariables true`. There is no test suite, so a clean build with no `sorry` is the
acceptance criterion for a `convertsM`.

`lake build Clap` has exactly one expected `sorry`: `poseidon.convertsM` in
[Examples/PoseidonProgram.lean](../Clap/Examples/PoseidonProgram.lean), which is unprovable by
design against the `opaque poseidonSpec` in that example. A second one is yours. The expected warnings
are exactly three: two `linter.dupNamespace` on `Util/Containers.lean:15`, and the `sorry`
warning above. (Earlier revisions of this guide also listed a `Clap.Lang.F8`
`dupNamespace` warning; there is no such warning — do not treat one as baseline.)

There *is* now an executable path, which there was not when this guide was written:
`Circuit.toCs` and `Circuit.toWg` both run. Use a smoke test as a cross-check, never as the
proof of a `convertsM`: a `native_decide` on one input says nothing about the `↔` you actually
have to establish.

### Two smoke-test styles, and when each works

**The constant-folding style**, [Poseidon.lean](../Clap/Poseidon/Poseidon.lean): build the
inputs with `mkConstant`, then evaluate the result ref against the *empty* varStore with
`return [{}, σ|z]` and `native_decide` on `.getResult 0 (HashConsSt.empty p)`.

This only works when every value is constant-folded through the hash-cons heap. **It cannot be
used for anything built on `num2bits`**, whose outputs are freshly allocated *variables* — they
have no value in `σ`, so the evaluation yields `none`.

**The lowering style**, for everything else. Take the gadget to a real constraint system and
run it, exactly as [Test/Backend.lean](../Clap/Test/Backend.lean) does for a hand-built `Circuit`:

```lean
private abbrev q : ℕ := 47
local instance instFactPrimeMyQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (…) : ClapM q Unit := do …        -- assert the expected result
private def sat (…) : Bool :=
  let c := check …
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat … = true := by native_decide
```

`getCircuit` / `getHashConsState` are what bridge `ClapM` to `Circuit`. Feed constants via
`FArray.ofBitVec` / `mkF` and use `0` public inputs, or allocate with `HashConsM.mkVar` and pass
values in the `#v[…]`. Four traps:

- **`wg.run` needs `[Fact (Nat.Prime p)]`, and `Primes.goldilocks` / `Primes.bn254` are
  `sorry`'d** in `Clap/Util/Primes.lean`. `native_decide` refuses anything depending on `sorry`, so
  pick a concrete prime with a real `by norm_num` proof. `47` and `1031` are cheap; `norm_num`
  also certifies `8589934609` (just over `2^33`, needed for 32-bit `binSum`) quickly.
- **Name the instance.** A bare `local instance : Fact (Nat.Prime q)` is auto-named from the
  type, so two files in the same namespace collide at import time with *"environment already
  contains"*. Give each an explicit distinct name.
- `private abbrev q` and `private def` keep the scaffolding out of the module's API.
- The gadget file now depends on `ConstraintSystem/toCs` and `WitnessGenerator/toWg`. That is
  acyclic — the back end does not import `Clap/Lang/` — but it does widen the import graph.

Worked examples live at the bottom of [FUnit/assert_range.lean](../Clap/Lang/Core/FUnit/assert_range.lean),
[FBitVec/binSum.lean](../Clap/Lang/Data/FBitVec/binSum.lean), [F/lessThan.lean](../Clap/Lang/Core/F/lessThan.lean)
and [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean).

## Checklist

- [ ] `lake build` passes with no `sorry`, no `admit`, and no warnings beyond the two
      pre-existing `linter.dupNamespace` ones from `Clap/Util/Containers.lean:15`.
- [ ] The proof uses `step` for each bind rather than manual `convertsM_bind` applications —
      except where two steps can each fail, which `step` cannot express; those use
      `convertsM_bind_and`.
- [ ] No `@[irreducible]` gate was `unfold`ed.
- [ ] If the constraints slot is not `True`, both `↔` directions are genuinely proved — not
      papered over by weakening the specification.
- [ ] One-off arithmetic helpers live in the gadget's own namespace, above `convertsM`.
- [ ] Any new `@[simp]` / `@[grind]` annotation is on a lemma that is genuinely a good rewrite
      in general, not just convenient here.
