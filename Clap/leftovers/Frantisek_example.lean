import Lean
import Qq

set_option linter.unusedVariables true
set_option autoImplicit false

abbrev Felt := Int

inductive Exp (var:Type _) where
  | v : var -> Exp var
  | c : Felt -> Exp var
  | op : Exp var -> Exp var -> Exp var

def Exp' : Type _ := (var:Type _) -> Exp var

def eval_e (e: Exp Felt) : Felt :=
  match e with
  | Exp.v v => v
  | Exp.c i => i
  | Exp.op l r => eval_e l + eval_e r

def eval_e' (e:Exp') := eval_e (e Felt)

def equiv_e (t:Exp') (s:Felt) := eval_e' t = s

notation : 65 t:65 "≡" s:66 => equiv_e t s

def eval_c (n:Felt) : (fun _ => Exp.c n) ≡ n := by
  simp [equiv_e, eval_e', eval_e]

def eval_op (el er:Exp') (l r:Felt) :
  el ≡ l → er ≡ r →
  (fun var => Exp.op (el var) (er var)) ≡ (l + r) := by
  intros hl hr;
  simp [equiv_e, eval_e'] at hl hr
  simp [equiv_e, eval_e', eval_e, *]

def a : ∃ e:Exp', e ≡ (1+2) := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )

-- This is only partially true, because we can always reduce an expression
-- (w/o variables) into an Felt, but we won't be producing the AST that we really want.
def parse_e (s:Felt) : ∃ e:Exp', e ≡ s := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )

def plonk (ql qr qo qm qc: Felt) (l r o:Felt) :=
  parse_e (ql * l + qr * r + qo * o + qm * l * r + qc)

-- we do not support abstracting over expressions
example : Felt -> Felt := fun x => x

-- /////////////////////

-- here we can add more types

inductive Wg (var:Type 0) where
  | nil : Wg var
  | eq0 : Exp var -> Wg var -> Wg var
  | lam : (var -> Wg var) -> Wg var
  | is_zero : Exp var -> (var -> Wg var) -> Wg var

def Wg' : Type 1 := (var:Type 0) -> Wg var

--//// source semantics /////////

-- we can restrict source term to be of type: Felt -> Felt -> ... -> Option Unit
-- first we take all the inputs, then we check them.

def ok : Felt -> Felt -> Option Unit :=
  fun x => fun y => if x=0 then none else if x=y then some () else none

-- this is not ok because we take an input, check it, then take another input
def not_ok : Felt -> Option (Felt -> Option Unit) :=
  fun x => if x = 0 then none else some (fun y => if x=y then some () else none)

/-
this kind of functions are allowed in Phoas, and we need them for:
- optimizations that need to introduce variables
  (which ones exactly? maybe Common Subexp Elim)
- lower to Cs to introduce additional inputs
However we probably don't need them in the source and we can restrict our
compilation to only the `ok` case.
-/


--///////////////////

-- example source
def eq0 (x:Felt) : Option Unit :=
  if (x = 0) then some () else none

-- example target
def eq0_wg : Wg' := fun var => Wg.lam (fun (x:var) => Wg.eq0 (Exp.v x) Wg.nil)

def nil_s (_:Felt) : Option Unit := some ()
def nil_wg : Wg' := fun var => Wg.lam (fun _:var => Wg.nil)

--/////////////////


-- do we need to prove additional properties of this semantics?

-- // Operational
def eval_wg (wg:Wg Felt) : Option (Wg Felt) :=
  match wg with
  | Wg.nil
  | Wg.lam _ => some wg
  | Wg.eq0 e wg =>
    if eval_e e = 0 then eval_wg wg else none
  | Wg.is_zero e k =>
    if eval_e e = 0 then eval_wg (k 1) else eval_wg (k 0)

-- no need for option
inductive eval_wg_rel : Wg Felt -> Wg Felt -> Prop where
  | nil : eval_wg_rel Wg.nil Wg.nil
  | lam (k:Felt -> Wg Felt) :
      eval_wg_rel (Wg.lam k) (Wg.lam k)
  | eq0_t
      (e:Exp Felt)
      (wg:Wg Felt)
      (h:eval_e e = 0) :
      eval_wg_rel (Wg.eq0 e wg) wg
  | is_zero
    (e:Exp Felt)
    (k:Felt -> Wg Felt)
    (b:Felt)
    (h:(eval_e e = 0 → b=1) ∧ (eval_e e ≠ 0 -> b=0)) :
    eval_wg_rel (Wg.is_zero e k) (k b)

inductive Equiv : {a:Type _} -> a -> Wg Felt -> Prop where
  | k :
    {b:Type _} ->
    (s:Felt -> b) ->
    (wg:Wg Felt) ->
    (k:Felt -> Wg Felt) ->
    (eval_wg_rel wg (Wg.lam k) -> ∀ x, Equiv (s x) (k x)) ->
    Equiv s (Wg.lam k)
  | unit :
    (wg:Wg Felt) ->
    (eval_wg_rel wg Wg.nil) ->
    Equiv (some ()) wg

notation : 65 s:65 " ≡ " t:66 => Equiv s (t Felt)


theorem Equiv.ext {α : Type _} {f : Felt → α} {g : Felt → Wg Felt} {g' : Wg Felt}
  (hint : g' = Wg.lam g)
  (h : Equiv f (Wg.lam g)) : Equiv f g' := by
  grind

example : ∃ wg':Wg', some () ≡ wg' := by
  refine ⟨?wg', ?heq⟩
  rotate_left
  constructor
  exact eval_wg_rel.nil

theorem simple : ∃ wg':Wg', nil_s ≡ wg' := by
  unfold Wg'
  refine ⟨?wg', ?heq⟩
  case' heq =>
    unfold nil_s
    refine Equiv.ext (g := ?g) (h := Equiv.k _ ?a _ (fun _ _ ↦ ?rest)) ?x
  case' wg' =>
    intros h; refine Wg.lam (fun _ ↦ ?_)
  case' rest =>
    apply Equiv.unit
  case' wg' =>
    refine Wg.nil
  case' rest =>
    exact eval_wg_rel.nil
  rfl
  exact Wg.nil -- Mmmmm ::thinking::. This is the lhs of the `eval_wg_rel (?g x✝️) Wg.nil`.

open Lean Meta Elab Tactic Qq

def unify (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let t : Q(Prop) ← goal.getType'
  let ~q($lhsQ = $rhsQ) := t | throwError "Expected ?mvar .. = _."
  let args ← lhsQ.getAppArgs.mapM instantiateMVars
  forallTelescopeReducing (←lhsQ.getAppFn.mvarId!.getType) fun fvs _ ↦ do
    let unifyingSide ← abstract (←instantiateMVars rhsQ) args fvs
    if !(← lhsQ.getAppFn.mvarId!.checkedAssign unifyingSide) then throwError "Unification failed."
  if ← mkEqRefl rhsQ >>= isDefEq (mkMVar goal) then return goal else return .none
  where
    abstract (e : Expr) (es fvs : Array Expr) : MetaM Expr := do
      -- The bit stolen from
      -- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.E2.9C.94.20Tricky.20metavariable.20unification
      let e ← (es.zip fvs).foldrM (init := e) fun (expr, fv) e => do
        pure <| (←kabstract e expr).instantiate1 fv
      let e ← es.foldrM (flip kabstract) e
      let e := e.instantiate fvs.reverse
      if ← isTypeCorrect e then
        return (← getLCtx).mkBinding true fvs e
      throwError s!"Cannot instantiate {fvs} in {e}."

elab "unify" : tactic => liftMetaTactic1 unify

def lessSimple : { wg':Wg' // nil_s ≡ wg' } := by
  unfold Wg'
  refine ⟨?wg', ?heq⟩
  case' heq =>
    unfold nil_s
    refine Equiv.ext (g := ?g) (h := Equiv.k _ ?a _ (fun _ _ ↦ ?rest)) ?x
  case' rest =>
    apply Equiv.unit
  case' rest =>
    exact eval_wg_rel.nil
  unify
  rfl
  constructor -- Mmmmm ::thinking::. This is the lhs of the `eval_wg_rel (?g x✝️) Wg.nil`.

/--
info: theorem lessSimple._proof_1 : Equiv nil_s (Wg.lam fun x ↦ Wg.nil) :=
id
  (Equiv.ext (Eq.refl (Wg.lam fun x ↦ Wg.nil))
    (Equiv.k (fun x ↦ some ()) Wg.nil (fun x ↦ Wg.nil) fun x x ↦ Equiv.unit Wg.nil eval_wg_rel.nil))
-/
#guard_msgs(info) in
#print lessSimple._proof_1
