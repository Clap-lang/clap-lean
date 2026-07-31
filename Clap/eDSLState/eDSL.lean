import Clap.eDSLState.Monad
import Mathlib.Tactic

namespace Clap.Edsl

variable {p : ℕ}

@[irreducible]
def eq0 (e : ExprRef) : ClapM p Unit := do
  tell #[.eq0 e]

@[irreducible]
def lam : ClapM p ExprRef := do
  tell #[.lam]
  let varIdx ← ClapM.alloc
  HashConsM.mkVar (p := p) varIdx

@[irreducible]
def share (e : ExprRef) : ClapM p (ExprRef) := do
  tell #[.share e]
  let varIdx ← ClapM.alloc
  HashConsM.mkVar (p := p) varIdx

@[irreducible]
def isZero (e : ExprRef) : ClapM p (ExprRef) := do
  tell #[.isZero e]
  let numAlloc ← ClapM.alloc -- (un)just one
  return numAlloc

@[irreducible]
def num2bits (width : ℕ) (e : ExprRef) : ClapM p (Vector (ExprRef) width) := do
  tell #[.num2bits width e]
  Vector.ofFnM fun _ ↦ do
    let varIdx ← ClapM.alloc
    HashConsM.mkVar (p := p) varIdx

section wellFormed

variable {numAlloc : ℕ} {e : ExprRef} {Γ : VarStore p} {σ}

@[aesop unsafe, grind .]
lemma eq0_wellFormed (h₁ : e < σ.exprs.size) (h₂ : [Γ,σ|e].isSome) :
  (eq0 e).wellFormed numAlloc Γ σ
:= by
  grind [eq0]

@[simp, grind .]
lemma lam_wellFormed :
  lam.wellFormed numAlloc Γ σ
:= by
  simp [lam]
  grind [lam]

@[simp, grind .]
lemma share_wellFormed {e : ExprRef} (h₁ : e < σ.exprs.size) (h₂ : [Γ,σ|e].isSome) :
  (share e).wellFormed e Γ σ
:= by
  grind [share]

@[simp, grind .]
lemma isZero_wellFormed {e : ExprRef} (h₁ : e < σ.exprs.size) (h₂ : [Γ,σ|e].isSome) :
  (isZero e).wellFormed e Γ σ
:= by
  grind [isZero]

@[simp]
abbrev num2bitsSansTellApply (p w numAlloc : ℕ) (σ : HashConsSt p) : ((List (Exp p ℕ) × CircuitState p) × ℕ) × HashConsSt p :=
  (List.ofFnM (n := w) (m := ClapM p)
    (
      fun _ => do
        let varIdx ← ClapM.alloc
        pure (Exp.v (p := p) varIdx)
    )).run numAlloc σ

def num2bitsButSane (width : ℕ) (e : ExprRef) (numAlloc : ℕ) (σ : HashConsSt p) : ClapM p (List (ExprRef)) := do
  tell #[.num2bits width e]
  num2bitsSansTellApply p width numAlloc

lemma map_toList_num2bits_eq_num2bitsButSane {w e} :
  Vector.toList <$> num2bits (p := p) w e = num2bitsButSane w e := by
  unfold num2bitsButSane num2bitsSansTellApply
  simp [num2bits]

lemma wellFormed_of_wellFormed_toList {α} {w} {action : ClapM p (Vector α w)}
  (h : (Vector.toList <$> action).wellFormed) :
  action.wellFormed := by
  aesop (add simp [ClapM.wellFormed, Clap.monads])

section

/-
Oh my god why are these so hard to write...

Wait why do I have to yoga after I changed to the array...
-/

@[simp, grind =]
lemma bind_alloc {α} {numAlloc} {f : ℕ → ClapM p α} :
  (ClapM.alloc >>= f) numAlloc = f numAlloc (numAlloc + 1) := by
  unfold_projs
  have : (getModify (m := (ClapM p)) (fun x => x + 1) numAlloc).2 = numAlloc + 1 := rfl
  have : (getModify (m := (ClapM p)) (fun x => x + 1) numAlloc).1.1 = numAlloc := by rfl
  simp [WriterT.run, ClapM.alloc, WriterT.mk, StateT.bind, Id]
  simp [StateT.map, Bind.bind, Pure.pure]
  aesop

@[simp, grind =]
lemma ClapM.map_apply {α β} {numAlloc} {f : α → β} {action : ClapM p α} :
  (f <$> action) numAlloc =
  ((f (action.getResult numAlloc), (action.getCircuit numAlloc)), (action.getState numAlloc)) := rfl

end

lemma _root_.List.ofFnM_eq_map_map_ofFnM {α β} {n : ℕ} {m} [Monad m] [LawfulMonad m] (f : (Fin n) → m α) (map_f : α → β):
  (List.ofFnM (fun idx => map_f <$> f idx)) =
  List.map map_f <$> List.ofFnM f
:= by
  induction n with
  | zero => simp
  | succ n h_n =>
    simp [List.ofFnM_succ, h_n]


lemma num2bitsSansTellApply_fst_fst {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).1.1 = (List.range' numAlloc w).map .v := by
  induction w generalizing numAlloc <;> aesop (add simp [List.ofFnM_succ, _root_.List.ofFnM_eq_map_map_ofFnM])

lemma num2bitsSansTellApply_fst_snd {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).1.2 = #[] := by
  induction w generalizing numAlloc <;> aesop (add simp List.ofFnM_succ)

lemma num2bitsSansTellApply_snd {w} {numAlloc} :
  (num2bitsSansTellApply p w numAlloc).2 = numAlloc + w := by
  induction w generalizing numAlloc <;> aesop (add simp List.ofFnM_succ) (add safe (by grind))

@[simp]
lemma getState_bind_tell {f : Unit → ClapM p (List (FixedExp p))} {l} :
  (tell l >>= f).getState = ClapM.getState (f ()) := rfl

@[simp]
lemma getCircuit_bind_tell {f : Unit → ClapM p (List (FixedExp p))} {l} {numAlloc} :
  (tell l >>= f).getCircuit numAlloc = l ++ (f () numAlloc).1.2 := by
  aesop (add simp Clap.monads)

@[simp]
lemma num2bits_wellFormed (width : ℕ) (e : FixedExp p) :
  (num2bits width e).wellFormed
:= by
  apply wellFormed_of_wellFormed_toList
  rw [map_toList_num2bits_eq_num2bitsButSane]
  intro numAlloc varStore
  unfold num2bitsButSane
  rw [getState_bind_tell, getCircuit_bind_tell]
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
  eval ((Edsl.eq0 e).getCircuit numAlloc) varStore numAlloc =
  eval #[CircuitusPlanus.eq0 e] varStore numAlloc
:= by
  simp [eq0]

@[simp, grind =]
lemma eval_edsl_lam
:
  eval ((Edsl.lam).getCircuit numAlloc) varStore numAlloc =
  eval #[CircuitusPlanus.lam] varStore numAlloc
:= by
  simp [Edsl.lam]

@[simp, grind =]
lemma eval_edsl_share
:
  eval ((Edsl.share e).getCircuit numAlloc) varStore numAlloc =
  eval #[CircuitusPlanus.share e] varStore numAlloc
:= by
  simp [Edsl.share]

@[simp, grind =]
lemma eval_edsl_isZero :
  eval ((Edsl.isZero e).getCircuit numAlloc) varStore numAlloc =
  eval #[CircuitusPlanus.isZero e] varStore numAlloc
:= by
  simp [Edsl.isZero]

-- example : eval (Edsl.isZero e numAlloc).1.2 varStore numAlloc = sorry := by
--   rw [eval_edsl_isZero]
--   rw [eval_singleton]
--   rw [CircuitResult.step_isZero]
--   rw [CircuitResult.assertAllocated_unconstrained]
--   rw [CircuitResult.get?_unconstrained]

--   simp only [CircuitResult.addConstraint_unconstrained]

--   simp only [CircuitResult.addConstraint_unconstrained, CircuitResult.alloc_mk,
--     Vector.range_one, Vector.map_mk, List.map_toArray, List.map_cons, zero_add, List.map_nil,
--     Vector.mk_zip_mk, List.zip_toArray, List.zip_cons_cons, List.zip_nil_right,
--     Std.ExtTreeMap.insertMany_single]

--   sorry

@[grind ←]
lemma getCircuit_ofFnM_of_getCircuit_eq_nil {α} (n: ℕ) (f : Fin n → ClapM p α) (numAlloc)
  (h_no_circuit: ∀ idx numAlloc, (f idx).getCircuit numAlloc = #[])
:
  (Vector.ofFnM f).getCircuit numAlloc =
  #[]
:= by
  induction n generalizing numAlloc with
  | zero => simp [Vector.ofFnM_zero]
  | succ n h_n =>
    rewrite [Vector.ofFnM_succ]
    simp [h_n, h_no_circuit]

@[simp, grind =]
lemma eval_edsl_num2bits
  {width : ℕ}
:
  eval ((Edsl.num2bits width e).getCircuit numAlloc) varStore numAlloc =
  eval #[CircuitusPlanus.num2bits width e] varStore numAlloc
:= by
  simp [Edsl.num2bits, getCircuit_ofFnM_of_getCircuit_eq_nil]

end

end CircuitState

/--
info: (((),
  #[Clap.CircuitusPlanus.lam,
    Clap.CircuitusPlanus.eq0 v0,
    Clap.CircuitusPlanus.share (1 + 1),
    Clap.CircuitusPlanus.eq0 1,
    Clap.CircuitusPlanus.eq0 2,
    Clap.CircuitusPlanus.eq0 v1,
    Clap.CircuitusPlanus.eq0 4]),
 2)
-/
#guard_msgs(whitespace := lax) in
#eval (test).run (p := 57) 0

end Edsl

end Clap
