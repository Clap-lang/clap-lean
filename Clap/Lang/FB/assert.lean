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

@[simp, grind .]
lemma assertMatchesLast_toLinear_unit
  {p : ℕ}
  [p.AtLeastTwo]
  {varStore1 varStore2 : VarStore p}
  {numAlloc : ℕ}
  {x : Unit}
:
  assertMatchesLast
    varStore1
    numAlloc
    (VarStoreSize.toLinear varStore2 x)
:= by
  unfold assertMatchesLast
  grind

lemma result_IsValid_iff
  {p : ℕ}
  [p.AtLeastTwo]
  {numAlloc : ℕ}
:
  unaryFunctionResultIsValidIff p (λ x => (FB.assert (p := p) x).getResult numAlloc)
:= by
  -- Pre-existing, uncompiled before this change: `getResult` always returns
  -- `Unit`, so the RHS of the iff is trivially `True`, making this claim
  -- "every `FB p` expression is valid" — false in general. Left unproved
  -- rather than inventing a new statement for unrelated pre-existing content.
  sorry

@[grind .]
lemma result_correct
  {p : ℕ}
  [p.AtLeastTwo]
:
  unaryFunctionResultIsCorrect p (!·) (FB.not (p := p))
:= by
  unfold unaryFunctionResultIsCorrect
  grind [FB.toRepresents_def]

lemma equiv (p : ℕ) [p.AtLeastTwo] :
  matchesUnaryMonadFunction p
    (spec_function := λ _ => ())
    (function := FB.assert)
    (allocatesN := 0)
    (constraints := λ input => input = Bool.true)
:= by
  -- The first conjunct (`unaryFunctionResultIsValidIff p assert`) asks for
  -- `IsValid.isValid varStore a ↔ IsValid.isValid varStore (assert a)`, but the
  -- RHS folds in `assert`'s constraint (`a = true`), which is strictly stronger
  -- than `a`'s own well-formedness (`a = true ∨ a = false`) — false when `a =
  -- false p`. This predates this change (pre-existing, uncompiled); leaving
  -- unproved rather than inventing a new predicate shape for assertions.
  sorry

end assert

end Clap.Edsl.Lang.FB
