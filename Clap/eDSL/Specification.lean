import Clap.eDSL.Basic
import Mathlib.Data.FinEnum

namespace Clap

namespace Spec

-- inductive Exp (p : ℕ) where
--   | v   (_ : ℕ)
--   | c   (_ : ZMod p)
--   | add (_ _ : Exp p )
--   | mul (_ _ : Exp p )
--   | sub (_ _ : Exp p )
--   deriving DecidableEq

abbrev Exp (p: ℕ) := Clap.Exp p ℕ

-- inductive Circuit (p : ℕ) : Type where
--   | nil
--   | eq0 (e : Exp p) (c : Circuit p)
--   | lam (cont : ℕ → Circuit p)
--   | share (e : Exp p) (cont : ℕ → Circuit p)
--   | isZero (e : Exp p) (cont : ℕ → Circuit p)
--   | num2bits (w : ℕ) (e : Exp p) (cont : List ℕ → Circuit p)
abbrev Circuit (p: ℕ) := (Clap.Circuit p ℕ)

structure AllocatedCircuit (p : ℕ) where
  varStore : Std.ExtTreeMap ℕ (ZMod p)
  circuit : Circuit p

-- def isVarAllocated {p : ℕ} (numAlloc : ℕ) (e : Exp p) : Bool :=
--   match e with
--   | .v n => n < numAlloc -- `n < varStore.size ↔ n ∈ varStore`; I think
--   | .add e₁ e₂ => isVarAllocated numAlloc e₁ && isVarAllocated numAlloc e₂
--   | .mul e₁ e₂ => isVarAllocated numAlloc e₁ && isVarAllocated numAlloc e₂
--   | .sub e₁ e₂ => isVarAllocated numAlloc e₁ && isVarAllocated numAlloc e₂
--   | .c _ => true

-- @[aesop safe [constructors, cases]]
-- inductive WFAllocatedCircuit (p : ℕ) : AllocatedCircuit p → Prop where
--   | nil {numAlloc : ℕ} :
--         WFAllocatedCircuit p ⟨numAlloc, .nil⟩
--   | eq0 {numAlloc : ℕ} {c : Circuit p} {e : Exp p}
--         (h : isVarAllocated numAlloc e)
--         (rec : WFAllocatedCircuit p ⟨numAlloc, c⟩) :
--         WFAllocatedCircuit p ⟨numAlloc, .eq0 e c⟩
--   | lam {numAlloc : ℕ} {cont : ℕ → Circuit p}
--         (rec : WFAllocatedCircuit p ⟨varStore.insert varStore.size.succ _, cont numAlloc⟩) :
--         WFAllocatedCircuit p ⟨numAlloc, .lam cont⟩
--   -- |

-- open Circuit in
-- def ex : Circuit 57 := .lam fun x ↦ .lam fun y ↦ .eq0 (.v 1) .nil

-- open WFAllocatedCircuit in
-- example : WFAllocatedCircuit 57 ⟨0, ex⟩ := by
--   unfold ex
  -- aesop (add simp ex)

def eval_expr {p : ℕ} (varStore : Std.ExtTreeMap ℕ (ZMod p)) (e : Exp p) : Option (ZMod p) := match e with
  | .c x => .some x
  | .v x => varStore.get? x
  | .add l r => do (←eval_expr varStore l) + (←eval_expr varStore r)
  | .sub l r => do (←eval_expr varStore l) - (←eval_expr varStore r)
  | .mul l r => do (←eval_expr varStore l) * (←eval_expr varStore r)

-- split varstore and circuit to not have to manually prove termination
-- TODO do we even still need AllocatedCircuit?
def eval_impl {p: ℕ} (varStore: Std.ExtTreeMap ℕ (ZMod p)) (circuit : Circuit p) : denotation (ZMod p) :=
  match circuit with
  | .nil =>
    .u
  | .lam k =>
    .l fun x =>
    let newIdx := varStore.size
    eval_impl (varStore.insert newIdx x) (k newIdx)
  | .eq0 e c =>
    if eval_expr varStore e = .some 0 then eval_impl varStore c else .n
  | .share e k =>
    let newIdx := varStore.size
    let val := eval_expr varStore e
    match val with
    | .some val => eval_impl (varStore.insert newIdx val) (k newIdx)
    | .none => .n
  | .isZero e k =>
    let invIdx := varStore.size
    let oIdx := invIdx + 1
    match eval_expr varStore e with
    | .some val =>
      let inv := val⁻¹
      if val = 0
      then eval_impl (varStore.insert invIdx inv |>.insert oIdx 1) (k oIdx)
      else eval_impl (varStore.insert invIdx inv |>.insert oIdx 0) (k oIdx)
    | .none =>
      .n
  | .num2bits w e k =>
      let val := eval_expr varStore e
      match val with
      | .some val =>
        if val.val < 2^w
        then
          let oldSize := varStore.size
          let idxs := List.range' oldSize w
          let bits := idxs.zip (num2bitsLsbPure w val)
          let varStore := varStore.insertMany bits
          eval_impl varStore (k idxs)
        else .n
      | .none => .n

def eval {p: ℕ} (circuit: AllocatedCircuit p) : denotation (ZMod p) :=
  eval_impl circuit.varStore circuit.circuit



def equiv {p: ℕ} {ResultT: Type}
  (varStore : Std.TreeMap ℕ (ZMod p))
  (circuit1 circuit2 : Edsl.CircuitContM p ℕ ResultT)
: Prop :=
  ∀ continuation, (
    eval ⟨varStore, (circuit1 continuation)⟩ =
    eval ⟨varStore, (circuit2 continuation)⟩
  )

lemma equiv_refl
  {p : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {ResultT : Type}
  {x : Edsl.CircuitContM p ℕ ResultT}
:
  equiv varStore x x
:= by
  aesop (add simp equiv)

lemma equiv_symm
  {p : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {ResultT : Type}
  {x y : Edsl.CircuitContM p ℕ ResultT}
:
  equiv varStore x y → equiv varStore y x
:= by
  aesop (add simp equiv)

lemma equiv_trans
  {p : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {ResultT : Type}
  {x y z : Edsl.CircuitContM p ℕ ResultT}
:
  equiv varStore x y →
  equiv varStore y z →
  equiv varStore x z
:= by
  aesop (add simp equiv)

-- TODO do we want a Setoid instance here?
-- varstore being a parameter rather than the relation being for all varstores makes it more difficult

def nix {p} (x : Exp p) : Edsl.CircuitContM p ℕ (Exp p) :=
  _root_.Pure.pure x

@[simp]
lemma _root_.Clap.Edsl.CircuitContM.nothing_def
  {p} (x : Exp p)
: nix x = pure x := rfl

open Edsl.CircuitContM in
lemma equiv_pure_unit {p : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
:
  equiv varStore (pure ()) (pure ())
:= equiv_refl

lemma equiv_eq0 {p: ℕ} {ResultT: Type}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  (a: Exp p)
  (rest : Edsl.CircuitContM p ℕ ResultT)
  (h_equiv: eval_expr varStore a = .some 0)
:
  equiv
    varStore
    (do
      Edsl.eq0 a
      rest
    )
    rest
:= by
  simp [equiv]
  intro continuation
  simp [eval, bind, Edsl.eq0, eval_impl, h_equiv]

-- TODO do we want Edsl.share to return an exp?
lemma equiv_share {p: ℕ} {ResultT: Type} {val : ZMod p} {other}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  (a: Exp p)
  (rest: (Exp p) → Edsl.CircuitContM p ℕ ResultT)
  (h_a : eval_expr varStore a = .some val)
:
  equiv
    varStore
    (do
      let x ← Edsl.share a
      rest (.v x)
    )
    other =
  equiv
    (varStore.insert (varStore.size) val)
    (rest (.v varStore.size))
    other
:= by
  simp [equiv, bind, Edsl.share, eval, eval_impl, h_a]
  apply Iff.intro
  . intro h continuation
    replace h := h continuation
    rw [h]
    done

def fails {p: ℕ} {ResultT: Type}
  (varStore : Std.TreeMap ℕ (ZMod p))
  (circuit : Edsl.CircuitContM p ℕ ResultT)
: Prop :=
    eval ⟨varStore, circuit (λ _result => .nil)⟩ =
    .n

lemma fails_eq0 {p: ℕ}
  (varStore : Std.TreeMap ℕ (ZMod p))
  (a: Exp p)
  (h_equiv: eval_expr varStore a ≠ .some 0)
:
  fails
    varStore
    (Edsl.eq0 a)
:= by
  simp [fails, eval, Edsl.eq0, eval_impl, h_equiv]

lemma fails_of_head_fails {p: ℕ} {ResultT: Type}
  (varStore : Std.TreeMap ℕ (ZMod p))
  (a: Exp p)
  (tail: Unit → Edsl.CircuitContM p ℕ ResultT)
  (h_fails: fails varStore (Edsl.eq0 a))
:
  fails
    varStore
    (bind (Edsl.eq0 a) tail)
:= by
  simp [fails, Edsl.eq0] at ⊢ h_fails
  simp [eval, eval_impl] at h_fails
  simp [h_fails, Edsl.eq0, eval, eval_impl, bind]

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

opaque Expr : Type
abbrev Cs := List Expr
abbrev OurM := StateM Cs
def someSpec (x : ZMod 57) : Option Unit := .none
-- example (cs : Cs) : cs.eval ≈ someSpec
-- `cs.eval Γ` (eval takes a `Γ`)
-- ^ does not work for any `Γ`, but WF `Γ`
-- 

-- The great Alin convincing:
-- 1. hand-compile (with tactics?)
-- 2. fail the contract, but deliver a model that is proven correct
--    (this includes full specs for everything as well)
-- 3. extract circom with Surveyor, prove with respect to 'the' specs
-- 4. `Cont`inue with `Cont`inuation monad
-- 5. use `ZKLean` / `Clean` (`ZKlean` > `Clean`?)
-- 6. use `State` monad?
-- 7. `#justFinishTheMetaCompiler`
-- 8. despair
