# Proving circuits in CLAP

How to state and prove that a `ClapM` circuit computes what you say it computes.

The judgement is `Clap.ConvertsM conversion action state val`
([`Clap/eDSLState/Convert.lean`](../Clap/eDSLState/Convert.lean)). Read it as a Hoare triple:
starting from `state`, running `action` produces expression references that denote the ideal
value `val`, emits a well-formed circuit, and emits constraints that hold.

```lean
structure ConvertsM (conversion : IdealT → List (ZMod p))
                    (action : ClapM p (List ExprRef))
                    (state : ClapMState p)
                    (val : IdealT) : Prop where
  result      : Converts conversion (action.getState state)
                         (action.getResult state.numAlloc state.σ) val
  wellFormed  : action.wellFormed state.numAlloc state.varStore state.σ
  constraints : (action.runAndEval state.numAlloc state.varStore state.σ).2.constraints
```

Each representation family (`F`, `FB`, `FUnit`, `FArray k`, `FList`) wraps it by fixing a
`toExprs` and a `serializeVal`:

```lean
X.ConvertsM a state v  ≡  Clap.ConvertsM X.serializeVal (X.toExprs <$> a) state v
```

Everything generic is stated in that `te <$> action` shape, so **one** lemma serves all five
families.

---

## Stating a spec

**1. One namespace per combinator, with four members.** Every primitive follows this:

```lean
namespace isZero
lemma wellFormed  … : (isZero a).wellFormed …
lemma converts    … : FB.Converts ((isZero a).getState state) … (a_val == 0)
lemma constraints … : ((isZero a).runAndEval …).2.constraints
lemma convertsM   … : FB.ConvertsM (isZero a) state (a_val == 0)
where
  result      := converts h_a
  wellFormed  := wellFormed h_a
  constraints := constraints h_a
end isZero
```

**2. Assemble `convertsM` with `where`, never `constructor`.** `Converts`'s fields are declared
`h_conversion, varSet_wf, expr_wf, value_eq`, but `constructor` presents them in the order
`varSet_wf, expr_wf, value_eq, h_conversion` — `h_conversion` comes *last* because
`value_eq`'s type depends on it. Named fields sidestep the trap.

**3. The spec is a function of ideal inputs only.** `ExprRef`s never appear in a spec value.
If you find yourself wanting one, you are stating a lemma about the implementation, not the
specification.

**4. Preconditions are `Converts` facts plus pure side conditions.** `F.Converts state idx
idx_val` and `len < p`, never `wellFormed` or `constraints` — those are *outputs* of
`ConvertsM`, produced by the proof, not assumed.

---

## Proving a `convertsM`

**5. Go forwards, never backwards.** Do not look for a bind rule that takes a
`function_val : IA → IB` and reconstructs the spec from it; unification cannot guess that
function. `Clap.ConvertsM.bind` takes the post-value free, which is what makes it usable:

```lean
lemma ConvertsM.bind
  (h_a : ConvertsM cA (teA <$> a) state va)
  (h_f : ConvertsM cB (teB <$> f (a.getResult state.numAlloc state.σ)) (a.getState state) vb)
: ConvertsM cB (teB <$> (a >>= f)) state vb
```

**6. One `clap_step` per `←` in the `do` block.**

```lean
clap_step (mkSub.convertsM h_a h_b) with h_sub
```

applies `ConvertsM.bind`, moves the goal to the post-state, re-bases every `Converts`
hypothesis onto it, and names this step's own result `h_sub`. Nothing goes between steps.

**7. Anything you still need after a step must be a `Converts` fact.** That is the only thing
the frame rule (`Clap.Converts.skip`) transports, and the only thing `clap_step` re-bases.

**8. Loops never get a hand-rolled induction.** Use the traversal rule with a `Stable` frame:

```lean
def Stable (P : ClapMState p → Prop) : Prop :=
  ∀ {β} (b : ClapM p β) st, b.wellFormed st.numAlloc st.varStore st.σ → P st → P (b.getState st)
```

`Stable.converts` says every `Converts` fact is stable; `Stable.and` / `Stable.all` combine
them. `FList.convertsM_mapM` then discharges a whole `List.mapM` from a single per-element
obligation that may assume `P`.

**9. Finish with `clap_finish`.** It tries `exact`, then `ConvertsM.congr_val` with an
automatic `rfl`/`simp`/`grind`, then leaves the serialisation equality as a goal.

**10. Pure reasoning lives in pure lemmas.** `ZMod` arithmetic, `Vector`/`List` identities and
spec reshaping go in standalone lemmas *above* the circuit proof. See `beq_natCast_comm` and
`oneHot_spec` in `Clap/Lang/F/F.lean` — between them they hold every `ZMod` fact that
`oneHotRaw`'s correctness needs, so the circuit proof itself has none.

---

## Worked example

`oneHotRaw` — the whole system in eleven lines:

```lean
lemma convertsM
  (h_idx : F.Converts state idx idx_val) (h_len : len < p)
: FArray.ConvertsM (oneHotRaw len idx) state (Vector.ofFn (fun i => i.val == idx_val.val))
:= by
  have : NeZero p := ⟨by omega⟩
  apply FArray.convertsM_of_convertsM_toList          -- Vector goal → List goal
  simp_rw [toList_map_oneHotRaw_eq_oneHotRaw']
  rw [oneHot_spec h_len]                              -- rule 10: spec reshaped by a pure lemma
  unfold oneHotRaw' oneHotRaw'_aux
  refine FList.convertsM_mapM (P := fun st => F.Converts st idx idx_val)
    Clap.Stable.converts h_idx ?_                     -- rule 8: the loop, once
  intro i _ st h_st
  clap_step (MkConstant.convertsM (x := (Nat.cast i : ZMod p))) with h_const  -- rule 6
  clap_finish (eq.convertsM h_st h_const)                                     -- rule 9
```

The previous version of this proof was 105 lines: an induction over
`(List.range' 0 len).reverse`, with the frame condition re-established by hand at every
unrolled step.

---

## Hygiene

**11. No `simp at *`.** It is the dominant proof-time cost in the old proofs, and the reason
they need the `set state := ….getState state` shadowing dance to keep the context readable.

**12. Don't shadow `state`.** `clap_step` moves the goal to the post-state for you.

**13. Name facts `h_<input>`.** Don't leave results bound to `this`; a later step will shadow
it silently.

**14. You do not need to keep `wellFormed`/`constraints` in scope.** The old style parked them
in the context so a closing `grind` could find them. `ConvertsM.bind` discharges all three
fields of `ConvertsM` itself, so there is no closing `grind` and nothing to park.

---

## Extending the system

**15. A new representation family adds four things and no more:** `toExprs`, `serializeVal`,
`Converts`, `ConvertsM` — plus *structural* lemmas specific to its container (`push`, `append`,
`cast`, `getElem`, …). Never copy `bind`, `map`, `pure`, `skip` or `converts_of_convertsM`;
those are generic. Define `ConvertsM` in the uniform `toExprs <$> action` shape or the generic
lemmas will not unify against it.

**16. A new generic lemma goes in `Clap/eDSLState/Convert.lean`,** stated in `te <$> action`
form for the same reason.

**17. Do not reintroduce a typeclass over representations.** `Convertible`/`ConvertibleM` was
tried and removed (the "LIST VERSION" commit). `F`, `FB` and `FArray`'s element type are all
`abbrev`s of `ExprRef`, so instance resolution keyed on the representation is ambiguous by
construction. Keep `conversion` and `toExprs` as ordinary unification variables.

---

## Where things live

| File | Contents |
|---|---|
| [`Clap/eDSLState/Convert.lean`](../Clap/eDSLState/Convert.lean) | `ClapMState`, `Converts`, `ConvertsM`, the generic combinators, `Stable` |
| [`Clap/eDSLState/ConvertTactic.lean`](../Clap/eDSLState/ConvertTactic.lean) | `clap_step`, `clap_finish` |
| [`Clap/eDSLState/Monad.lean`](../Clap/eDSLState/Monad.lean) | `ClapM`, the getters, `wellFormed`, `runAndEval` |
| [`Clap/Lang/F/F.lean`](../Clap/Lang/F/F.lean) | the five families and every circuit proof |

Build the live target with:

```bash
lake build Clap.Lang.F.F
```

`lake build` (default target) does **not** pass: `Clap.lean` imports `Clap.Lang.All`, which
pulls in `Clap/Lang/FB/*.lean` and `Clap/Lang/F/eq.lean`. Those files predate the current
`abbrev F := ExprRef` and are not part of the live build.
