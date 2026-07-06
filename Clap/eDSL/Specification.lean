import Clap.eDSL.Basic
import Mathlib.Data.FinEnum

namespace Clap

namespace Spec

inductive Exp (p : ℕ) where
  | v   (_ : ℕ)
  | c   (_ : ZMod p)
  | add (_ _ : Exp p )
  | mul (_ _ : Exp p )
  | sub (_ _ : Exp p )
  deriving DecidableEq

inductive Circuit (p : ℕ) : Type where
  | nil
  | eq0 (e : Exp p) (c : Circuit p)
  | lam (cont : ℕ → Circuit p)
  | share (e : Exp p) (cont : ℕ → Circuit p)
  | isZero (e : Exp p) (cont : ℕ → Circuit p)
  | num2bits (w : ℕ) (e : Exp p) (cont : List ℕ → Circuit p)

structure AllocatedCircuit (p : ℕ) where
  varStore : Std.TreeMap ℕ (ZMod p)
  circuit : Circuit p

def isVarAllocated {p : ℕ} (numAlloc : ℕ) (e : Exp p) : Bool :=
  match e with
  | .v n => n < numAlloc
  | _ => true

-- @[aesop safe [constructors, cases]]
-- inductive WFAllocatedCircuit (p : ℕ) : AllocatedCircuit p → Prop where
--   | nil {numAlloc : ℕ} :
--         WFAllocatedCircuit p ⟨numAlloc, .nil⟩
--   | eq0 {numAlloc : ℕ} {c : Circuit p} {e : Exp p}
--         (h : isVarAllocated numAlloc e)
--         (rec : WFAllocatedCircuit p ⟨numAlloc, c⟩) :
--         WFAllocatedCircuit p ⟨numAlloc, .eq0 e c⟩
--   | lam {numAlloc : ℕ} {cont : ℕ → Circuit p}
--         (rec : WFAllocatedCircuit p ⟨numAlloc.succ, cont numAlloc⟩) :
--         WFAllocatedCircuit p ⟨numAlloc, .lam cont⟩
--   -- | 

-- open Circuit in
-- def ex : Circuit 57 := .lam fun x ↦ .lam fun y ↦ .eq0 (.v 1) .nil

-- open WFAllocatedCircuit in
-- example : WFAllocatedCircuit 57 ⟨0, ex⟩ := by
--   unfold ex
  -- aesop (add simp ex)

def eval_expr {p : ℕ} (varStore : Std.TreeMap ℕ (ZMod p)) (e : Exp p) : Option (ZMod p) := match e with
  | .c x => .some x
  | .v x => varStore.get? x
  | .add l r => do (←eval_expr varStore l) + (←eval_expr varStore r)
  | .sub l r => do (←eval_expr varStore l) - (←eval_expr varStore r)
  | .mul l r => do (←eval_expr varStore l) * (←eval_expr varStore r)

def eval {p: ℕ} (circuit : AllocatedCircuit p) : denotation (ZMod p) :=
-- Defining parametric eval like this does not seem easy
-- either the cont members in constructors like share and isZero need to be switched to exp and we
-- make eval have them pass through a .c, then prove that that's equivalent to them making a new variable
-- or we need to be able to non-destructively update the varStore, or show that it was already sufficient
-- for us to keep making new variables. This could be fixing var to nat and keeping a counter of trace length,
-- it could be making var a Fintype that keeps changing, or other options
-- There may be far reaching changes required for either updating share, isZero etc to return exps, or for
-- making additional claims about var here
  let ⟨varStore, circuit⟩ := circuit
  match circuit with
  | .nil =>
    .u
  | .lam k =>
    .l fun x =>
    let newIdx := varStore.size
    eval ⟨varStore.insert newIdx x, k newIdx⟩
  | .eq0 e c =>
    if eval_expr varStore e = .some 0 then eval ⟨varStore, c⟩ else .n
  | .share e k =>
    let newIdx := varStore.size
    let val := eval_expr varStore e
    match val with
    | .some val => eval ⟨varStore.insert newIdx val, k newIdx⟩
    | .none => .n
  | .isZero e k =>
    let invIdx := varStore.size
    let oIdx := invIdx + 1
    match eval_expr varStore e with
    | .some val =>
      let inv := val⁻¹
      if val = 0
      then eval ⟨varStore.insert invIdx inv |>.insert oIdx 1, k oIdx⟩
      else eval ⟨varStore.insert invIdx inv |>.insert oIdx 0, k oIdx⟩
    | .none =>
      .n
  | .num2bits w e k =>
      if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n

def equiv {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (circuit1 circuit2 : Edsl.CircuitContM p var ResultT)
: Prop :=
  ∀ continuation, (
    eval varStore (circuit1 continuation) =
    eval varStore (circuit2 continuation)
  )
  
-- instance {p : ℕ} {var : Type} {ResultT : Type}
--   : Setoid (Edsl.CircuitContM p var ResultT) where
--   r c₁ c₂ := ∀ Γ, equiv Γ c₁ c₂
--   iseqv   := {
--     refl  := by aesop (add simp equiv)
--     symm  := by aesop (add simp equiv)
--     trans := by aesop (add simp equiv)
--   }

def nix {p var} (x : Exp p var) : Edsl.CircuitContM p var (Exp p var) :=
  _root_.Pure.pure x

@[simp]
lemma _root_.Clap.Edsl.CircuitContM.nothing_def {p var} (x : Exp p var) : nix x = pure x := rfl

-- TODO prove these lemmas
-- TODO finish set of spec utility lemmas
-- TODO Setoid
open Edsl.CircuitContM in
lemma equiv_pure {p : ℕ} {var : Type}
  {a b : Exp p var}
  {varStore : var → ZMod p}
  (h_equiv : eval_expr varStore a = eval_expr varStore b)
: 
  equiv varStore (pure a) (pure b)
:= by
  sorry

lemma equiv_eq0 {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (a: Exp p var)
  (rest: Edsl.CircuitContM p var ResultT)
  (h_equiv: eval_expr varStore a = 0)
:
  equiv
    varStore
    (do
      Edsl.eq0 a
      rest
    )
    rest
:= by
  sorry

def fails {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (circuit : Edsl.CircuitContM p var ResultT)
: Prop :=
  ∀ continuation,
    eval varStore (circuit continuation) =
    .n

lemma fails_eq0 {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (a: Exp p var)
  (h_equiv: eval_expr varStore a ≠ 0)
:
  fails
    varStore
    (Edsl.eq0 a)
:= by
  sorry

lemma fails_of_head_fails {p: ℕ} {var: Type} {MidT ResultT: Type}
  (varStore : var → ZMod p)
  (head: Edsl.CircuitContM p var MidT)
  (tail: MidT → Edsl.CircuitContM p var ResultT)
  (h_fails: fails varStore head)
:
  fails
    varStore
    (bind head tail)
:= by
  simp [fails, bind] at ⊢ h_fails
  intro continuation
  rw [h_fails]

-- TODO
-- this is not true in general
-- but can perhaps be proven for all Edsl constructs as head
-- lemma fails_of_tail_fails {p: ℕ} {var: Type} {MidT ResultT: Type}
--   (varStore : var → ZMod p)
--   (head: Edsl.CircuitContM p var MidT)
--   (tail: MidT → Edsl.CircuitContM p var ResultT)
--   (h_fails: ∀ x, fails varStore (tail x))
-- :
--   fails
--     varStore
--     (bind head tail)
-- := by
--   simp [fails, bind] at ⊢ h_fails
--   intro continuation

-- TODO this requires the implementation of eval
lemma fails_of_tail_fails {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (a: Exp p var)
  (tail: Unit → Edsl.CircuitContM p var ResultT)
  (h_fails: ∀ x, fails varStore (tail x))
:
  fails
    varStore
    (bind (Edsl.eq0 a) tail)
:= by
  simp [fails, bind] at ⊢ h_fails
  intro continuation
  simp [Edsl.eq0]
  sorry

def matches_spec {p: ℕ} {var : Type} {ResultT : Type}
  (varStore : var → ZMod p)
  (guard : Prop)
  (circuit : Edsl.CircuitContM p var ResultT)
  (result : ResultT)
: Prop :=
  (guard → (equiv
    varStore
    circuit
    (pure result)
  )) ∧ (¬guard → fails varStore circuit)

namespace MonadExperiment

abbrev ΓM (p : ℕ) (var : Type) := StateM (var → ZMod p)

abbrev Γ {p : ℕ} {var : Type} (x : var) : ΓM p var (ZMod p) := get >>= fun Γ ↦ return Γ x

def eval_expr {p : ℕ} {var : Type} (e : Exp p var) : ΓM p var (ZMod p) := do
  match e with
  | .c x => return x
  | .v x => Γ x
  | .add l r => return (←eval_expr l) + (←eval_expr r)
  | .sub l r => return (←eval_expr l) - (←eval_expr r)
  | .mul l r => return (←eval_expr l) * (←eval_expr r)

def eval {p: ℕ} {var: Type} (circuit : Circuit p var) : ΓM p var (denotation var) :=
  sorry

def equiv {p : ℕ} {var : Type} {ResultT : Type}
  (Γ : var → ZMod p)
  (circuit1 circuit2 : Edsl.CircuitContM p var ResultT)
   : Prop :=
  ∀ continuation, (eval (circuit1 continuation)).run' Γ = (eval (circuit2 continuation)).run' Γ

open Edsl.CircuitContM in
lemma equiv_pure {p : ℕ} {var : Type}
  {a b : Exp p var}
  {varStore : var → ZMod p}
  (h_equiv : (eval_expr a).run' varStore = (eval_expr b).run' varStore)
: 
  equiv varStore (pure a) (pure b)
:= by
  sorry

end MonadExperiment

end Spec

end Clap
