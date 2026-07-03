import Clap.eDSL.Basic

namespace Clap

namespace Spec

def eval_expr {p: ℕ} {var: Type} (varStore : var → ZMod p) (e: Exp p var) : ZMod p := match e with
  | .c x => x
  | .v x => varStore x
  | .add l r => eval_expr varStore l + eval_expr varStore r
  | .sub l r => eval_expr varStore l - eval_expr varStore r
  | .mul l r => eval_expr varStore l * eval_expr varStore r

def eval {p: ℕ} {var: Type} (varStore : var → ZMod p) (circuit: Circuit p var) : denotation var :=
  sorry
-- Defining parametric eval like this does not seem easy
-- either the cont members in constructors like share and isZero need to be switched to exp and we
-- make eval have them pass through a .c, then prove that that's equivalent to them making a new variable
-- or we need to be able to non-destructively update the varStore, or show that it was already sufficient
-- for us to keep making new variables. This could be fixing var to nat and keeping a counter of trace length,
-- it could be making var a Fintype that keeps changing, or other options
-- There may be far reaching changes required for either updating share, isZero etc to return exps, or for
-- making additional claims about var here
-- match circuit with
--   | .nil =>
--       .u
--   | .lam k =>
--       .l fun x => eval varStore (k x)
--   | .eq0 e c =>
--       if e.eval = 0 then eval varStore c else .n
--   | .share e k =>
--       if ∃ x: var, varStore x = eval_expr varStore e ∧ eval varStore (k x) = .u
--       then .u
--       else .n
--   | .isZero e k =>
--       if e.eval = 0 then (k 1).eval else (k 0).eval
--   | .num2bits w e k =>
--       if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n

def equiv {p: ℕ} {var: Type} {ResultT: Type}
  (varStore : var → ZMod p)
  (circuit1 circuit2 : Edsl.CircuitContM p var ResultT)
: Prop :=
  ∀ continuation, (
    eval varStore (circuit1 continuation) =
    eval varStore (circuit2 continuation)
  )

-- TODO prove these lemmas
-- TODO finish set of spec utility lemmas
-- TODO Setoid
lemma equiv_pure {p: ℕ} {var: Type}
  (varStore : var → ZMod p)
  (a b: Exp p var)
  (h_equiv: eval_expr varStore a = eval_expr varStore b)
:
  equiv
    varStore
    (pure a)
    (pure b)
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

end Spec

end Clap
