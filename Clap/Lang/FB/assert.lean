import Clap.Lang.FB.FB
import Clap.Lang.FB.not

namespace Clap.Edsl.Lang.FB

def assert {p : ℕ} [p.AtLeastTwo] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (not a)

namespace assert

@[simp, grind .]
lemma isAlwaysValid_unit
  {p : ℕ}
  [p.AtLeastTwo]
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {f : Edsl.CircuitStateM p Unit}
:
  IsValid.isValid varStore (f.getResult numAlloc)
:= by
  trivial

@[simp, grind =]
lemma toIdeal_unit
  {p : ℕ}
  {varStore : VarStore p}
  {x : Unit}
:
  Convert.toIdeal varStore x = .some ()
:= by
  trivial

@[simp, grind =]
lemma getResult_unit
  {p : ℕ}
  {numAlloc : ℕ}
  {f : Edsl.CircuitStateM p Unit}
:
  f.getResult numAlloc = ()
:= rfl

@[grind =]
lemma step_eq0_fb
  {p : ℕ}
  [p.AtLeastTwo]
  {a : FB p}
  {result : CircuitResult p}
:
  [result|CircuitusPlanus.eq0 a]ₛ =
  result.addConstraint ([result.varStore|a] = [result.varStore|false p])
:= rfl

@[grind =]
lemma assert_constraints
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {a : FB p}
  {numAlloc : ℕ}
  (h: IsValid.isValid varStore a)
:
  [varStore, numAlloc|(a.assert.getCircuit numAlloc)]ₑ.constraints =
  ((Convert.toIdeal varStore a).get (by grind) = Bool.true)
:= by
  unfold assert
  grind

@[grind =]
lemma assert_numAlloc
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {a : FB p}
  {numAlloc : ℕ}
:
  [varStore, numAlloc|(a.assert.getCircuit numAlloc)]ₑ.numAlloc =
  numAlloc
:= by
  unfold assert
  grind

@[grind =]
lemma assert_frameRule
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {a : FB p}
  {numAlloc : ℕ}
:
  ∀ n, n < numAlloc →
    [varStore, numAlloc|(a.assert.getCircuit numAlloc)]ₑ.varStore[n]? =
    varStore[n]?
:= by
  intro n h_n
  unfold assert
  grind

@[simp, grind =]
lemma toLinear_unit
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore : VarStore p}
:
  VarStoreSize.toLinear varStore () =
  #v[]
:= by
  rfl

@[simp, grind .]
lemma assertMatchesLast_empty
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
:
  assertMatchesLast
    varStore
    numAlloc
    #v[]
:= by
  unfold assertMatchesLast
  grind

set_option allowUnsafeReducibility true
attribute [local reducible] instVarStoreSizeUnit

set_option pp.all true in
lemma equiv (p : ℕ) [p.AtLeastTwo] :
  matchesUnaryMonadFunction p
    (spec_function := λ _ => ())
    (function := FB.assert)
    (allocatesN := 0)
    (constraints := λ input => input = Bool.true)
:= by
  intro a varStore numAlloc h_isValid
  have : (a.assert.runAndEval numAlloc varStore) =
    ⟨
      (a.assert.getResult numAlloc),
      [varStore, numAlloc|a.assert.getCircuit numAlloc]ₑ
    ⟩
  := by rfl
  grind

end assert

end Clap.Edsl.Lang.FB
