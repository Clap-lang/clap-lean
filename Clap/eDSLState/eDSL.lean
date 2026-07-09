import Clap.eDSLState.Monad

namespace Clap.Edsl

variable {p : ℕ}

-- TODO split this into a file
@[irreducible]
def eq0 (e : FixedExp p) : CircuitStateM p Unit := do
  tell [.eq0 e]

@[irreducible]
def lam : CircuitStateM p (FixedExp p) := do
  tell [.lam]
  let numAlloc ← CircuitStateM.alloc
  return .v numAlloc

@[irreducible]
def share (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
  tell [.share e]
  let numAlloc ← CircuitStateM.alloc
  return (.v numAlloc)

@[irreducible]
def isZero (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
  tell [.isZero e]
  let numAlloc ← CircuitStateM.alloc -- (un)just one
  return .v numAlloc

@[irreducible]
def num2bits (width : ℕ) (e : FixedExp p) : CircuitStateM p (Vector (FixedExp p) width) := do
  tell [.num2bits width e]
  Vector.ofFnM fun _ ↦ do
    let varIdx ← CircuitStateM.alloc
    return .v varIdx

def test : CircuitStateM p Unit := do
  let x ← lam
  eq0 x
  let y ← share (.add 1 1)
  discard <| [1, 2, y].mapM eq0
  eq0 4

namespace CircuitState

section

variable {e : FixedExp p} {numAlloc : ℕ} {varStore : Std.ExtTreeMap ℕ (ZMod p)}

@[simp, grind =]
lemma eval_edsl_eq0
:
  eval (Edsl.eq0 e numAlloc).1.2 varStore numAlloc =
  eval [CircuitusPlanus.eq0 e] varStore numAlloc
:= by
  simp only [eq0, Clap.monads]

@[simp, grind =]
lemma eval_edsl_lam
:
  eval (Edsl.lam numAlloc).1.2 varStore numAlloc =
  eval [CircuitusPlanus.lam] varStore numAlloc
:= by
  simp [
    Clap.monads,
    Edsl.lam
  ]

@[simp, grind =]
lemma eval_edsl_share
:
  eval (Edsl.share e numAlloc).1.2 varStore numAlloc =
  eval [CircuitusPlanus.share e] varStore numAlloc
:= by
  simp [
    Clap.monads,
    Edsl.share
  ]

@[simp, grind =]
lemma eval_edsl_isZero :
  eval (Edsl.isZero e numAlloc).1.2 varStore numAlloc =
  eval [CircuitusPlanus.isZero e] varStore numAlloc
:= by
  simp [
    Clap.monads,
    Edsl.isZero
  ]

example : eval (Edsl.isZero e numAlloc).1.2 varStore numAlloc = sorry := by
  -- simp
  rw [eval_edsl_isZero]
  rw [eval_singleton]
  rw [CircuitResult.step_isZero]
  rw [CircuitResult.assertAllocated_withNoConstraints]
  rw [CircuitResult.get?_withNoConstraints]

  simp only [CircuitResult.addConstraint_withNoConstraints]
  
  simp only [CircuitResult.addConstraint_withNoConstraints, CircuitResult.alloc_mk,
    Vector.range_one, Vector.map_mk, List.map_toArray, List.map_cons, zero_add, List.map_nil,
    Vector.mk_zip_mk, List.zip_toArray, List.zip_cons_cons, List.zip_nil_right,
    Std.ExtTreeMap.insertMany_single]

  sorry

-- TODO, trying to use this instead of the set, have, subst combo
@[simp]
lemma match_pair
  (α β γ)
  (a : Id (α × β))
  (f : α → β → γ)
:
  match a with
    | (x, y) => f x y
  = f a.1 a.2
:= rfl

@[simp, grind =]
lemma eval_edsl_num2bits
  (width : ℕ)
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
:
  Edsl.CircuitState.eval (Edsl.num2bits width e numAlloc).1.2 varStore numAlloc =
  ⟨
    numAlloc + width,
    varStore.insertMany
      ((Vector.map (fun x => x + numAlloc) (Vector.range width)).zip
        (num2bitsLsbPureV width ((FixedExp.eval varStore.get? e).getD 0))),
    (e.eval varStore.get?).isSome
  ⟩
:= by
  simp [
    Clap.monads,
    Edsl.num2bits,
    CircuitStateM.alloc
  ]
  unfold StateT.pure StateT.map StateT.bind
  simp [Clap.monads]
  set x := @Vector.ofFnM (CircuitStateM p) _ _ _ _ _
  have : x = ⟨x.1, x.2⟩ := rfl
  rewrite [this]; clear this
  subst x
  simp [Clap.monads]

end

end CircuitState

/--
info: (((),
  [Clap.CircuitusPlanus.lam,
   Clap.CircuitusPlanus.eq0 v0,
   Clap.CircuitusPlanus.share (1 + 1),
   Clap.CircuitusPlanus.eq0 1,
   Clap.CircuitusPlanus.eq0 2,
   Clap.CircuitusPlanus.eq0 v1,
   Clap.CircuitusPlanus.eq0 4]),
 2)
-/
#guard_msgs in
#eval (test).run (p := 57) 0

end Edsl

end Clap
