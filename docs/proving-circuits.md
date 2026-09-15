---
name: proving-circuits
description: Rules for proving a CLAP gadget's ConvertsM lemma - the step tactic, the three proof skeletons, the induction recipe, and failure modes.
when-to-use: You are proving a convertsM lemma, or a CLAP proof is stuck.
---

# Proving CLAP circuits

Read [clap-agent-guide.md](clap-agent-guide.md) first, and
[specifying-circuits.md](specifying-circuits.md) for the shape of the statement you are proving.

## What you actually have to show

`ConvertsM` is a three-field structure ([Convert/Base.lean](../Clap/eDSLState/Convert/Base.lean)):

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
```

## The `step` tactic

Defined at [Clap/Lang/F/Tactics.lean:160-217](../Clap/Lang/F/Tactics.lean#L160-L217). This is
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
- `step` takes an arbitrary term, not just a library lemma. Feeding it an induction hypothesis
  is idiomatic: `step @h_k fvals_base vals_base this as mapM` in
  [FArray/sum.lean](../Clap/Lang/FArray/sum.lean), and `step h_len as mapM` in
  [FArray/OneHotRaw.lean](../Clap/Lang/FArray/OneHotRaw.lean).

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
| The body uses `+`, `-`, `*` on `F p` | `rw [add_def]` / `rw [sub_def]` / `rw [mul_def]` |
| The body should be read as its generalised helper | `simp [←<helper>.eq_def]` |
| The body is a `mapM`/`foldlM` | rewrite with the `_succ` equation first |

`sub_def` in [FB/eq.lean](../Clap/Lang/FB/eq.lean) and `simp [←sum'.eq_def]` in
[FArray/sum.lean](../Clap/Lang/FArray/sum.lean) are the worked cases.

## Skeleton 1 — straight-line composition

`unfold` → one `step` per bind → close the tail call with `convertsM_of_convertsM`.

From [FB/eq.lean](../Clap/Lang/FB/eq.lean), complete:

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

`convertsM_of_convertsM h h_val h_constraints` leaves exactly two goals: the value equality and
the constraints bi-implication. Close them with `rfl`, `grind`, `simp` or `trivial`.

When a step changes the conversion (`F` ↔ `FB`), do the cast with a `have` before applying —
[FB/not.lean](../Clap/Lang/FB/not.lean):

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
[FArray/singleOneArray.lean](../Clap/Lang/FArray/singleOneArray.lean):

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

From [F/mkAdd.lean](../Clap/Lang/F/mkAdd.lean):

```lean
  unfold mkAdd
  constructor
  · exact hashConsM_converts h_a h_b
  . grind
  . grind [ClapM.runAndEval]
```

The `Converts` half is factored into its own lemma and proved by destructuring both inputs:

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
`eDSL.lean` — [FUnit/eq0.lean](../Clap/Lang/FUnit/eq0.lean) is the template. The `wellFormed`
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

[FArray/sum.lean](../Clap/Lang/FArray/sum.lean). The trick is reassociating the vector so the
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

[FArray/OneHotRaw.lean](../Clap/Lang/FArray/OneHotRaw.lean). Usually easier: `List` has more
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
| *"Conclusion unchanged; spec missing for: …"* | the action's head is not `bind`/`map` | `unfold` first; or `rw [add_def/sub_def/mul_def]`; or use `step_state` |
| *"Failed to unify. Bad."* | the supplied `ConvertsM` does not match the head of the bind | check the conversion (`F` vs `FB`), and whether you need a cast lemma first |
| *"Assumptions of shape `Converts` refer to multiple states"* | a hypothesis was not carried forward | it should have been reframed by `step`; if you introduced it manually, apply `converts_skip` yourself |
| *"Expected ConvertsM. Got: …"* | you passed a `Converts`, not a `ConvertsM`, to `step` | use `step` with the `.convertsM` lemma; a bare `Converts` is a `have`, not a step |
| Goal explodes into raw `WriterT`/`StateT` terms | you unfolded an `@[irreducible]` gate | undo; go through `getResult_*` / `getCircuit_*` / `wellFormed_*` instead |
| The constraints `↔` will not close and looks false | your slot-5 condition is wrong (often spuriously `True`) | fix the specification, not the proof |
| An extra unexplained goal at the end of a Skeleton-2 proof | the `convertsM_bind` implications for a non-`True` constraint | that is soundness/completeness; prove them |
| The constraints goal reads `… ↔ (True → True → … → P)` and `constructor`/`intro` then mismatches | each preceding `True`-constraint step contributes one `True →` via `convertsM_bind` | a bare `simp` absorbs them, but a targeted script must strip them first: `simp only [true_implies]`. See [FB/assertBool.lean](../Clap/Lang/FB/assertBool.lean) |

## Verification

```
lake build Clap                          # everything
lake build Clap.Lang.FArray.sum          # one gadget and its dependencies
```

Lean `v4.32.0`, Mathlib pinned to `v4.32.0`, `autoImplicit false`,
`linter.unusedVariables true`. There is no test suite and no `native_decide` path for the new
model, so a clean build with no `sorry` is the entire acceptance criterion.

## Checklist

- [ ] `lake build` passes with no `sorry`, no `admit`, and no warnings beyond the two
      pre-existing `linter.dupNamespace` ones from `Clap/eDSLState/Wheels.lean:15`.
- [ ] The proof uses `step` for each bind rather than manual `convertsM_bind` applications.
- [ ] No `@[irreducible]` gate was `unfold`ed.
- [ ] If the constraints slot is not `True`, both `↔` directions are genuinely proved — not
      papered over by weakening the specification.
- [ ] One-off arithmetic helpers live in the gadget's own namespace, above `convertsM`.
- [ ] Any new `@[simp]` / `@[grind]` annotation is on a lemma that is genuinely a good rewrite
      in general, not just convenient here.
