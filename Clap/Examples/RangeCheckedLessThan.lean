import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FUnit.assert_range
import Clap.Model.AllocatedProgram
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.PublicInput
import Clap.Model.WitnessGenerator.toWg
/-!
# Using a range established earlier in the circuit

`lessThan` does not range-check its operands, so its `convertsM` takes their bounds as
hypotheses, which nothing can supply for a top-level input. This program range-checks both
operands itself and then compares them, and `rangeCheckedLessThan.convertsM` states its
constraint with **no** hypothesis on `a_val` or `b_val`: its only value hypotheses are `Converts`
facts at arbitrary values, which is exactly what input allocation provides.

The proof is the pattern in [docs/proving-circuits.md](../../docs/proving-circuits.md),
§Using a range established earlier in the circuit: `lessThan.convertsM_unchecked` holds for every
input, and `convertsM_bind_guard` rewrites its raw constraint under the range checks' constraint.

`rangeCheckedLessThanProgram.getConstraints_iff` then states it for the whole program, with `a`
and `b` as public inputs and no hypothesis on the input vector at all; see
[docs/public-inputs.md](../../docs/public-inputs.md).
-/

namespace Clap

open Lang

variable {p : ℕ}

/-- Range-check `a` and `b` to `w` bits, then assert `a < b`. -/
def rangeCheckedLessThan (w : ℕ) (a b : F p) : ClapM p Unit := do
  assert_range w a
  assert_range w b
  let lt ← lessThan w a b
  assert lt

namespace rangeCheckedLessThan

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {w : ℕ}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (hw : 2 ^ (w + 1) < p)
:
  ConvertsM FUnit.conversion (rangeCheckedLessThan w a b) state ()
    (a_val.val < 2 ^ w ∧ b_val.val < 2 ^ w ∧ a_val.val < b_val.val)
:= by
  unfold rangeCheckedLessThan
  -- The `do` block nests to the right. Group the two range checks, so that one action
  -- establishes both bounds.
  rw [← bind_assoc]
  have hA := assert_range.convertsM (w := w) h_a
  have hAB := convertsM_bind_and (function := fun _ => assert_range w b) hA
    (assert_range.convertsM (w := w) (converts_skip hA h_b))
  -- The comparison and its `assert` at arbitrary values; slot 5 is
  -- `lessThanOk w a_val b_val ∧ lessThanRaw w a_val b_val = true`.
  have hLt := lessThan.convertsM_unchecked (w := w) (converts_skip hAB h_a) (converts_skip hAB h_b)
  have hT := convertsM_bind_and (function := assert) hLt (assert.convertsM hLt.result)
  -- Under the range checks' constraint, the bridge lemmas turn that into `a_val.val < b_val.val`.
  refine convertsM_of_convertsM (convertsM_bind_guard hAB hT ?_) rfl and_assoc
  rintro ⟨ha, hb⟩
  rw [lessThan.lessThanRaw_eq ha hb hw]
  simp [lessThan.lessThanOk_of ha hb hw]

end rangeCheckedLessThan

/-- `rangeCheckedLessThan` as a whole program: `a` and `b` are public inputs `0` and `1`. -/
def rangeCheckedLessThanProgram (w : ℕ) : AllocatedProgram p where
  InputT := F p × F p
  program := fun input ↦ rangeCheckedLessThan w input.1 input.2
  numAlloc := 2
  allocate := do
    let a ← mkInputF 0
    let b ← mkInputF a.2
    return (a.1, b.1)

namespace rangeCheckedLessThanProgram

/-! Allocating from the empty heap is concrete: the two refs are `0` and `1`, and the heap holds
exactly the two variable nodes. -/

lemma allocate_getResult {w : ℕ} :
  (rangeCheckedLessThanProgram (p := p) w).allocate.getResult (HashConsSt.empty p) = (0, 1)
:= by
  simp [rangeCheckedLessThanProgram, mkInputF, HashConsM.getResult_mkVar,
    HashConsM.getHashConsState_mkVar, HashConsSt.empty, HashConsSt.pushExpr, HashConsSt.size]

lemma allocate_exprs {w : ℕ} :
  ((rangeCheckedLessThanProgram (p := p) w).allocate.getHashConsState (HashConsSt.empty p)).exprs
    = #[.v 0, .v 1]
:= by
  simp [rangeCheckedLessThanProgram, mkInputF, HashConsM.getResult_mkVar,
    HashConsM.getHashConsState_mkVar, HashConsM.getHashConsState_bind, HashConsSt.empty,
    HashConsSt.pushExpr, HashConsSt.size]

/-- The bridge: allocation `i` converts to position `i` of the prover's vector, in the varStore
`getConstraints` builds. -/
lemma converts_input {w : ℕ} {input : Vector (ZMod p) 2} (i : ℕ) (h_i : i < 2) :
  Converts F.conversion
    ⟨Std.ExtTreeMap.ofArray (Array.map Prod.swap input.toArray.zipIdx) compare,
     (rangeCheckedLessThanProgram (p := p) w).allocate.getHashConsState (HashConsSt.empty p), 2⟩
    (i : F p) input[i]
:= by
  have h_deref : *ₑ⦃(i : F p),
      (rangeCheckedLessThanProgram (p := p) w).allocate.getHashConsState (HashConsSt.empty p)⦄
      = some (.v i) := by
    simp [Expr.deref, allocate_exprs]
    interval_cases i <;> rfl
  have h_wf : ⦃(i : F p),
      (rangeCheckedLessThanProgram (p := p) w).allocate.getHashConsState
        (HashConsSt.empty p)⦄.wellFormed :=
    Expr.wellFormed_iff_isSome.mpr (by rw [h_deref]; rfl)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro ⟨j, h_j⟩
    simp at h_j ⊢
    subst h_j
    unfold Expr.varSet_wellFormed Expr.varSet
    grind
  · intro ⟨j, h_j⟩
    simp at h_j ⊢
    subst h_j
    exact h_wf
  · intro ⟨j, h_j⟩
    simp at h_j ⊢
    subst h_j
    rw [eval_eq_evalRec h_wf, evalRec_eq_of_deref_eq_some_v h_deref]
    obtain ⟨⟨input⟩, h_input⟩ := input
    simp [Std.ExtTreeMap.toArray_eq_toArray, Std.ExtTreeMap.ofList_eq_insertMany_empty,
      Std.ExtTreeMap.getElem?_insertMany_eq_getElem?]

/-- The program's constraint system holds at `input` exactly when both inputs fit in `w` bits
and the first is less than the second. There is no hypothesis on `input`. -/
theorem getConstraints_iff [p.AtLeastTwo] {w : ℕ} (hw : 2 ^ (w + 1) < p)
    {input : Vector (ZMod p) 2} :
    (rangeCheckedLessThanProgram w).getConstraints input ↔
      input[0].val < 2 ^ w ∧ input[1].val < 2 ^ w ∧ input[0].val < input[1].val
:= by
  have h_run : (rangeCheckedLessThanProgram (p := p) w).allocate.run (HashConsSt.empty p) =
      ((0, 1), (rangeCheckedLessThanProgram (p := p) w).allocate.getHashConsState
        (HashConsSt.empty p)) :=
    Prod.ext allocate_getResult rfl
  unfold AllocatedProgram.getConstraints AllocatedProgram.getCircuit
  rw [h_run]
  exact (rangeCheckedLessThan.convertsM (w := w)
    (converts_input (w := w) (input := input) 0 (by omega))
    (converts_input (w := w) (input := input) 1 (by omega)) hw).constraints

end rangeCheckedLessThanProgram

section examples

/-! Lowered with `Circuit.toWg` / `Circuit.toCs` on two public inputs, as in
[FUnit/assert_range.lean](../Lang/Core/FUnit/assert_range.lean). `q = 1031` exceeds `2^9`, so
`hw` holds at `w = 8`. -/

private abbrev q : ℕ := 1031

local instance instFactPrimeRangeCheckedLessThanQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- `rangeCheckedLessThan 8` on two public inputs. -/
private def rangeChecked : ClapM q Unit := do
  let a ← liftM (HashConsM.mkVar (p := q) 0)
  let b ← liftM (HashConsM.mkVar (p := q) 1)
  rangeCheckedLessThan 8 a b

/-- The same comparison without the range checks. -/
private def bare : ClapM q Unit := do
  let a ← liftM (HashConsM.mkVar (p := q) 0)
  let b ← liftM (HashConsM.mkVar (p := q) 1)
  let lt ← lessThan 8 a b
  assert lt

private def sat (c : ClapM q Unit) (a b : ZMod q) : Bool :=
  let circ  := c.getCircuit 2 (HashConsSt.empty q)
  let cache := c.getHashConsState 2 (HashConsSt.empty q)
  (circ.toCs cache 2).run ((circ.toWg cache 2).run #v[a, b])

example : sat rangeChecked 3 5 = true := by native_decide
example : sat rangeChecked 5 3 = false := by native_decide
-- `a` out of range
example : sat rangeChecked 300 5 = false := by native_decide
-- `b` out of range, though `3 < 300`. `lessThan` rejects this pair by itself too: its offset
-- `3 - 300 + 2^8` wraps to `990 ≥ 2^9`, so its own `num2bits` check fails.
example : sat rangeChecked 3 300 = false := by native_decide
example : sat bare 3 300 = false := by native_decide
-- Here only the range checks stand in the way. `1030 - 0 + 2^8` wraps to `255`, which passes the
-- offset check with top bit `0`, so the bare comparison accepts the claim `1030 < 0`.
example : sat bare 1030 0 = true := by native_decide
example : sat rangeChecked 1030 0 = false := by native_decide

end examples

end Clap
