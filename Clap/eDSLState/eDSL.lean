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

section wellFormed

lemma eq0_wellFormed (e : FixedExp p) :
  (eq0 e).wellFormed
:= by
  simp [Clap.monads, eq0, CircuitStateM.wellFormed]

lemma lam_wellFormed :
  (lam : CircuitStateM p _).wellFormed
:= by
  simp [Clap.monads, lam, CircuitStateM.wellFormed]

lemma share_wellFormed (e : FixedExp p) :
  (share e).wellFormed
:= by
  simp [Clap.monads, share, CircuitStateM.wellFormed]

lemma isZero_wellFormed (e : FixedExp p) :
  (isZero e).wellFormed
:= by
  simp [Clap.monads, isZero, CircuitStateM.wellFormed]

lemma num2bits_wellFormed (width : ℕ) (e : FixedExp p) :
  (num2bits width e).wellFormed
:= by
  unfold CircuitStateM.wellFormed num2bits
  intro numAlloc varStore
  simp [Clap.monads]
  split
  expose_names
  simp
  set varStore := @varStore.insertMany _ _ _ _ (Vector _ width) _ _
  have (α β : Type) (a : α × β) (b: α) (c: β) : a = (b, c) → b = a.1 := by
    grind
  have := this _ _ _ _ _ heq
  rewrite [this]
  unfold StateT.bind CircuitStateM.alloc StateT.map StateT.pure pure Id.instMonad at ⊢ heq
  unfold_projs at ⊢ heq
  simp at ⊢ heq
  rewrite [heq]
  simp

  -- have (α) (m : Type → Type) (k : ℕ) (f : Fin k → m α) [Monad m] [LawfulMonad m] : (Vector.finRange k).mapM f = Vector.ofFnM f := by
  --   clear *-k f
  --   induction k with
  --     | zero => simp
  --     | succ k h =>
  --       rewrite [Vector.ofFnM_succ', Vector.finRange_succ]
  --       specialize h (fun i => f i.succ)
  --       rewrite [←h]
  --       simp [Vector.cast, ]
  --       have (xs : Vector (Fin (k + 1)) (k + 1)) : Functor.map (Vector.toList) (Vector.mapM f xs) = List.mapM f xs.toList := by
  --         simp [Vector.toList_]

  --       done
  --   done

  -- I dislike Vector.ofFnM now
  -- also Vector.ofMapM
  -- :(
  -----------


  -- induction width with
  -- | zero => simp [Clap.monads]
  -- | succ width h =>
  --   simp [Vector.ofFnM_succ, Clap.monads] at ⊢ h
  --   have : (match
  --     Vector.ofFnM
  --       (fun x =>
  --         StateT.bind CircuitStateM.alloc fun x =>
  --           StateT.map (fun x_1 => (x_1.1, x.2 ++ x_1.2)) (StateT.pure (Exp.v x.1, [])))
  --       numAlloc with
  --   | (a, s) => ((a.1, CircuitusPlanus.num2bits width e :: a.2), s)) = sorry
  --   := by
  --     done

  --   split
  --   split at h
  --   expose_names
  --   split at heq
  --   expose_names
  --   dsimp at ⊢ h
  --   rewrite [
  --     show s = s_2 + 1 by grind,
  --     show a = (a_2.1.push (Exp.v s_2), a_2.2) by grind
  --   ]
  --   have : a_1 = a_2 := by grind
  --   have : s_1 = s_2 := by grind
  --   simp_all



  --   rewrite [h]
  --   specialize h numAlloc varStore

  --   simp [
  --     Clap.monads,
  --   ]



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
