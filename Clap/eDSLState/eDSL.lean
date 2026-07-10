import Clap.eDSLState.Monad
import Mathlib.Tactic

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

section wellFormed

@[simp]
lemma eq0_wellFormed (e : FixedExp p) :
  (eq0 e).wellFormed
:= by
  simp [Clap.monads, eq0, CircuitStateM.wellFormed]

@[simp]
lemma lam_wellFormed :
  (lam : CircuitStateM p _).wellFormed
:= by
  simp [Clap.monads, lam, CircuitStateM.wellFormed]

@[simp]
lemma share_wellFormed (e : FixedExp p) :
  (share e).wellFormed
:= by
  simp [Clap.monads, share, CircuitStateM.wellFormed]


@[simp]
lemma isZero_wellFormed (e : FixedExp p) :
  (isZero e).wellFormed
:= by
  simp [Clap.monads, isZero, CircuitStateM.wellFormed]

@[simp]
abbrev num2bitsSansTellApply (p w numAlloc : ℕ) : ((List (Exp p ℕ) × CircuitState p) × ℕ) :=
  List.ofFnM (n := w) (m := CircuitStateM p)
    (
      fun _ => do
        let varIdx ← CircuitStateM.alloc
        pure (Exp.v (p := p) varIdx)
    )
    numAlloc

def num2bitsButSane (width : ℕ) (e : FixedExp p) : CircuitStateM p (List (FixedExp p)) := do
  tell [.num2bits width e]
  num2bitsSansTellApply p width

lemma map_toList_num2bits_eq_num2bitsButSane {w e} :
  Vector.toList <$> num2bits (p := p) w e = num2bitsButSane w e := by
  unfold num2bitsButSane num2bitsSansTellApply 
  simp [num2bits]
  
lemma wellFormed_of_wellFormed_toList {α} {w} {action : CircuitStateM p (Vector α w)}
  (h : (Vector.toList <$> action).wellFormed) :
  action.wellFormed := by
  aesop (add simp [CircuitStateM.wellFormed, Clap.monads])

section

/-
Oh my god why are these so hard to write...
-/

@[simp, grind =]
lemma bind_alloc {α} {numAlloc} {f : ℕ → CircuitStateM p α} :
  (CircuitStateM.alloc >>= f) numAlloc = f numAlloc (numAlloc + 1) := rfl

@[simp, grind =]
lemma CircuitStateM.map_apply {α β} {numAlloc} {f : α → β} {action : CircuitStateM p α} :
  (f <$> action) numAlloc =
  ((f (action numAlloc).1.1, (action numAlloc).1.2), (action numAlloc).2) := rfl

end

lemma num2bitsSansTellApply_fst_fst {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).1.1 = (List.range' numAlloc w).map .v := by
  induction w generalizing numAlloc <;> aesop (add simp List.ofFnM_succ)

lemma num2bitsSansTellApply_fst_snd {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).1.2 = [] := by
  induction w generalizing numAlloc <;> aesop (add simp List.ofFnM_succ)

lemma num2bitsSansTellApply_snd {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).2 = numAlloc + w := by
  induction w generalizing numAlloc <;> aesop (add simp List.ofFnM_succ) (add safe (by grind))

@[simp]
lemma getNumAlloc_bind_tell {f : Unit → CircuitStateM p (List (FixedExp p))} {l} :
  (tell l >>= f).getNumAlloc = CircuitStateM.getNumAlloc (f ()) := rfl

@[simp]
lemma getState_bind_tell {f : Unit → CircuitStateM p (List (FixedExp p))} {l} {numAlloc} :
  (tell l >>= f).getState numAlloc = l ++ (f () numAlloc).1.2 := by
  aesop (add simp Clap.monads)

@[simp]
lemma num2bits_wellFormed (width : ℕ) (e : FixedExp p) :
  (num2bits width e).wellFormed
:= by
  apply wellFormed_of_wellFormed_toList
  rw [map_toList_num2bits_eq_num2bitsButSane]
  intro numAlloc varStore
  unfold num2bitsButSane
  rw [getNumAlloc_bind_tell, getState_bind_tell]
  rw [CircuitState.eval_append, num2bitsSansTellApply_fst_snd]
  suffices (num2bitsSansTellApply p width numAlloc).2 = numAlloc + width by simpa
  rw [num2bitsSansTellApply_snd]

end wellFormed

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
  rw [eval_edsl_isZero]
  rw [eval_singleton]
  rw [CircuitResult.step_isZero]
  rw [CircuitResult.assertAllocated_unconstrained]
  rw [CircuitResult.get?_unconstrained]

  simp only [CircuitResult.addConstraint_unconstrained]

  simp only [CircuitResult.addConstraint_unconstrained, CircuitResult.alloc_mk,
    Vector.range_one, Vector.map_mk, List.map_toArray, List.map_cons, zero_add, List.map_nil,
    Vector.mk_zip_mk, List.zip_toArray, List.zip_cons_cons, List.zip_nil_right,
    Std.ExtTreeMap.insertMany_single]

  sorry

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
  unfold getModify
  unfold modifyGet
  unfold instMonadStateOfMonadStateOf
  dsimp only
  conv =>
    enter [1, 1, 1, 1, 2, 1, x, s, 1]
    unfold_projs
    unfold StateT.modifyGet


    skip
  simp [Clap.monads]
  set x := @Vector.ofFnM (CircuitStateM p) _ _ _ _ _
  have : x = ⟨x.1, x.2⟩ := rfl
  rewrite [this]; clear this
  subst x
  simp [Clap.monads, CircuitResult.addConstraint_unconstrained]

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
