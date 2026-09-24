import Clap.Lang.Core.F.mkF
import Clap.Lang.Gate.eq0
import Clap.Tactic.Step
/-!
# Two assertions that can fail together

`step` goes through `convertsM_bind`, so after stepping an action whose constraint is `C₁` it
leaves the continuation at `C₁ → S`. The continuation emits its own constraint `C₂`, and
`ConvertsM`'s constraint field is an `↔`, so that goal forces `¬C₁ → C₂` (`step_obligation`):
`step` needs the two constraints never to fail together.

`twoEq0 a b` asserts `a = 0`, then `b = 0`. At `a = b = 1` both fail, so no spec `S` makes the
goal `step` leaves provable for all inputs (`twoEq0.step_no_go`). `convertsM_bind_and` proves the
natural spec in one line (`twoEq0.convertsM`). A hypothesis that rules out the first failure lets
`step` through (`twoEq0.convertsM_of_eq_zero`). `twoEq0.convertsM_of_eq_zero_or_eq_zero` is the
`step` proof of the natural spec, commented where it fails: it is stuck on exactly
`a_val = 0 ∨ b_val = 0`, and goes through only with that as a hypothesis.

See [docs/proving-circuits.md](../../docs/proving-circuits.md),
§When `step` does not apply — two assertions that can fail together.
-/

namespace Clap

open Lang

variable {p : ℕ}

/-- Assert `a = 0`, then `b = 0`. -/
def twoEq0 (a b : F p) : ClapM p Unit := do
  eq0 a
  eq0 b

/-- The goal `step` leaves after an action with constraint `C₁` is the continuation at `C₁ → S`.
Against the continuation's own spec at `C₂`, it forces `C₂` whenever `C₁` fails, for every `S`. -/
private lemma step_obligation
  {α} {conversion : Conversion p α} {cont : ClapM p α} {state}
  {val val' : conversion.IdealT} {C₁ C₂ S : Prop}
  (h_goal : ConvertsM conversion cont state val (C₁ → S))
  (h_cont : ConvertsM conversion cont state val' C₂)
: ¬C₁ → C₂ :=
  fun h => (h_cont.constraints.symm.trans h_goal.constraints).mpr (fun h1 => absurd h1 h)

namespace twoEq0

/-- No spec rescues `step`: whatever `S` is, even one that depends on the inputs, the goal
`step eq0.convertsM h_a as _` leaves is false at `a = b = 1`. -/
theorem step_no_go [p.AtLeastTwo] (S : ZMod p → ZMod p → Prop) :
  ¬ ∀ (state : ClapMState p) (a b : F p) (a_val b_val : ZMod p),
      Converts F.conversion state a a_val → Converts F.conversion state b b_val →
      ConvertsM FUnit.conversion (eq0 b) ((eq0 a).getState state) () (a_val = 0 → S a_val b_val)
:= by
  intro h
  haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
  have h1 := (mkF.convertsM (state := ⟨∅, HashConsSt.empty p, 0⟩) (a := (1 : ZMod p))).result
  have h_b := converts_skip (eq0.convertsM h1) h1
  exact one_ne_zero (step_obligation (h _ _ _ 1 1 h1 h1) (eq0.convertsM h_b) one_ne_zero)

/-- The natural spec, with no hypothesis on the inputs, by `convertsM_bind_and`. -/
lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FUnit.conversion (twoEq0 a b) state () (a_val = 0 ∧ b_val = 0)
:= by
  unfold twoEq0
  have h_eq0 := eq0.convertsM h_a
  exact convertsM_bind_and h_eq0 (eq0.convertsM (converts_skip h_eq0 h_b))

/-- With `a_val = 0` assumed, the first assertion cannot fail, so `step` goes through: the
continuation's obligation `b_val = 0 ↔ (a_val = 0 → a_val = 0 ∧ b_val = 0)` holds. -/
lemma convertsM_of_eq_zero
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (h_a_val : a_val = 0)
:
  ConvertsM FUnit.conversion (twoEq0 a b) state () (a_val = 0 ∧ b_val = 0)
:= by
  unfold twoEq0
  step eq0.convertsM h_a as eq0_a
  apply convertsM_of_convertsM (eq0.convertsM h_b)
  . rfl
  . simp [h_a_val]

/-- The spec of `convertsM`, by `step`. The proof is stuck on `a_val = 0 ∨ b_val = 0`, so it goes
through only with that as a hypothesis; without it, `step_no_go` shows no proof exists. -/
lemma convertsM_of_eq_zero_or_eq_zero
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (h_or : a_val = 0 ∨ b_val = 0)
:
  ConvertsM FUnit.conversion (twoEq0 a b) state () (a_val = 0 ∧ b_val = 0)
:= by
  unfold twoEq0
  -- No error here: `step` applies `convertsM_bind` whatever the constraints are. It leaves the
  -- continuation at `a_val = 0 → a_val = 0 ∧ b_val = 0`, plus the side goal
  -- `a_val = 0 ∧ b_val = 0 → a_val = 0`, which its `intros; trivial` does not close.
  step eq0.convertsM h_a as eq0_a
  . -- Stepping `eq0 b` too would not help: it is the tail, not a bind, so `step` warns
    -- "Conclusion unchanged; spec missing for: eq0 b" and only renames the goal.
    apply convertsM_of_convertsM (eq0.convertsM h_b)
    . rfl
    . -- The failure: `b_val = 0 ↔ (a_val = 0 → a_val = 0 ∧ b_val = 0)`. That is
      -- `a_val = 0 ∨ b_val = 0`, false at `a = b = 1`. Without `h_or`, `grind` and `tauto`
      -- fail, and `simp` errors with "simp made no progress".
      fail_if_success (clear h_or; grind)
      fail_if_success (clear h_or; tauto)
      fail_if_success (clear h_or; simp)
      rcases h_or with h | h <;> simp [h]
  . exact And.left

end twoEq0

end Clap
