set_option autoImplicit false
set_option linter.unusedVariables true

--import Mathlib.Data.ZMod.Basic
--import Mathlib.FieldTheory.Finite.Basic

-- variable p : Nat
-- variable [Fact (Nat.Prime p)]

namespace Phoas

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

-- here we can add more types

-- Cs can be used wherever a Circuit is used
-- true if it is Cs
inductive Circuit (var:Type 0) : Bool -> Type where
  | nil : Circuit var true
  | eq0 : {b:Bool} -> Exp var -> Circuit var b -> Circuit var b
  | lam : {b:Bool} -> (var -> Circuit var b) -> Circuit var b
  | share : {b:Bool} -> Exp var -> (var -> Circuit var b) -> Circuit var false
  | is_zero : {b:Bool} -> Exp var -> (var -> Circuit var b) -> Circuit var false

def Circuit' (var:Type 0) : Type 0 := Σ (b:Bool), Circuit var b
def Circuit'' : Type 1 := (var:Type 0) -> Circuit' var
def Cs (var:Type 0) : Type 0 := Circuit var true
def Cs' : Type 1 := (var:Type 0) -> Cs var


-- namespace Boh

-- def is_cs (c:Circuit Unit) : Bool :=
--   open Circuit in
--   match c with
--   | nil => true
--   | eq0 _ c => is_cs c
--   | lam k => is_cs (k ())
--   | _ => false

-- def is_cs' (c:Circuit') : Bool := is_cs (c Unit)

-- example : is_cs (Circuit.lam (fun x => Circuit.eq0 (Exp.v x) Circuit.nil)) = true := rfl

-- example : is_cs (Circuit.lam (fun x => Circuit.share (Exp.v x) (fun _x => Circuit.nil))) = false := rfl

-- def Cs var := { c:Circuit var // ∃ c':Circuit', c' var = c ∧ is_cs' c' }
-- def Cs' := fun var => Cs var

-- end Boh

-- -- we could remove this type and add an index to Circuit, which would save us from defining again the semantics of Cs
-- inductive Cs (var:Type 0) where
--   | nil : Cs var
--   | eq0 : Exp var -> Cs var -> Cs var
--   | lam : (var -> Cs var) -> Cs var

-- def Cs' : Type 1 := (var:Type 0) -> Cs var

/-
Warning: var must be kept abstract, if var is fixed we can write bogus examples
-/

-- E.g. here v 0 is not bound by any lam
example : Cs Nat := Circuit.eq0 (Exp.v 0) Circuit.nil

-- This is the right way, keeping var abstract, don't even need to name it
example : Cs' := fun _ => Circuit.lam (fun x => Circuit.eq0 (Exp.v x) Circuit.nil)

-- do we need to prove additional properties of this semantics?

-- big-step operational semantics
namespace Functional
namespace Circuit

-- functional
def eval {b:Bool} (c:Circuit Felt b) : Option (Circuit Felt b) :=
  match c with
  | Circuit.nil => by
    have : b = true := sorry
    exact some c
  | Circuit.lam _ => some c
  | Circuit.eq0 e c =>
    if eval_e e = 0 then eval c else none
  | Circuit.share e k => eval (k (eval_e e))
  | Circuit.is_zero e k =>
    if eval_e e = 0 then eval (k 1) else eval (k 0)

def eval' (c:Circuit') : Option (Circuit Felt) := eval (c Felt)

end Circuit

-- namespace Cs
-- -- functional
-- def eval (cs:Cs Felt) : Option (Cs Felt) :=
--   match cs with
--   | Cs.nil
--   | Cs.lam _ => some cs
--   | Cs.eq0 e cs =>
--     if eval_e e = 0 then eval cs else none

-- def eval' (cs:Cs') : Option (Cs Felt) := eval (cs Felt)

-- end Cs

-- maybe strong bisimulation is equivalent to equality + functional extensionality? But then the two types must be merged.
-- in that way if there are two huge term that are syntactically the same we can stop the simulation.

inductive s_bisim : (l r: Option (Circuit Felt)) -> Prop where
  | false
      : s_bisim none none
  | true
      : s_bisim (some Circuit.nil) (some Circuit.nil)
  | sync
      (kl:Felt -> Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (h: ∀ x, s_bisim (Circuit.eval (kl x))
                            (Circuit.eval (kr x)))
      : s_bisim (some (Circuit.lam kl)) (some (Circuit.lam kr))

def s_bisim' (l r : Circuit') := s_bisim (some (l Felt)) (some (r Felt))

inductive rw_bisim : (l r: Option (Circuit Felt)) -> Prop where
  | false
      : rw_bisim none none
  | true
      : rw_bisim (some Circuit.nil) (some Circuit.nil)
  | sync
      (kl:Felt -> Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (h: ∀ x, s_bisim (Circuit.eval (kl x))
                       (Circuit.eval (kr x)))
      : rw_bisim (some (Circuit.lam kl)) (some (Circuit.lam kr))
  | async
      (l:Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (x:Felt)
      (h: rw_bisim l (Circuit.eval (kr x)))
      : rw_bisim l (Circuit.lam kr)

def rw_bisim' (l r : Circuit') := rw_bisim (some (l Felt)) (some (r Felt))

end Functional

namespace Relational
-- relational, no need for option

namespace Circuit
inductive eval : Circuit Felt -> Circuit Felt -> Prop where
  | nil : eval Circuit.nil Circuit.nil
  | lam
      (k:Felt -> Circuit Felt)
      : eval (Circuit.lam k) (Circuit.lam k)
  | eq0_t
      (e:Exp Felt)
      (c:Circuit Felt)
      (h:eval_e e = 0)
      : eval (Circuit.eq0 e c) c
  | is_zero
      (e:Exp Felt)
      (k:Felt -> Circuit Felt)
      (b:Felt)
      (h:(eval_e e = 0 → b=1) ∧ (eval_e e ≠ 0 -> b=0))
      : eval (Circuit.is_zero e k) (k b)

end Circuit

inductive s_bisim : (l r: Circuit Felt) -> Prop where
  | true
      : s_bisim Circuit.nil Circuit.nil
  | sync
      (kl:Felt -> Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (lres:Circuit Felt)
      (rres:Circuit Felt)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Circuit.eval (kr x) rres) ->
        s_bisim lres rres)
      : s_bisim (Circuit.lam kl) (Circuit.lam kr)

def s_bisim' (l : Circuit') (r : Circuit') := s_bisim (l Felt) (r Felt)

inductive rw_bisim : (l: Circuit Felt) -> (r: Circuit Felt) -> Prop where
  | true
      : rw_bisim Circuit.nil Circuit.nil
  | sync
      (kl:Felt -> Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (lres:Circuit Felt)
      (rres:Circuit Felt)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Circuit.eval (kr x) rres) ->
        rw_bisim lres rres)
      : rw_bisim (Circuit.lam kl) (Circuit.lam kr)
  | async
      (l:Circuit Felt)
      (kr:Felt -> Circuit Felt)
      (rres:Circuit Felt)
      (x:Felt)
      (h: Circuit.eval (kr x) rres -> rw_bisim l rres)
      : rw_bisim l (Circuit.lam kr)

def rw_bisim' (l r: Circuit') := rw_bisim (l Felt) (r Felt)

end Relational

namespace Gen_trace

-- a list with continuations
inductive Wg where
  | nil : Wg
  | cons : Felt -> Wg -> Wg
  | input : (Felt -> Wg) -> Wg

def to_wg (wg:Circuit Felt) : Wg :=
  match wg with
  | Circuit.nil => Wg.nil
  | Circuit.eq0 _ wg => to_wg wg
  | Circuit.lam k => Wg.input (fun i => to_wg (k i))
  | Circuit.share e k =>
    let e := eval_e e
    Wg.cons e (to_wg (k e))
  | Circuit.is_zero e k =>
    let e := if eval_e e = 0 then 1 else 0
    Wg.cons e (to_wg (k e))

def to_wg' (wg:Circuit') : Wg := to_wg (wg Felt)

-- def wrap (wg:Cs Felt) (gt:Wg) : Cs Felt :=
--   match wg with
--   | Cs.nil => Cs.nil
--   | Cs.eq0 e wg => Cs.eq0 e (wrap wg gt)
--   | Cs.lam k =>
--     match gt with
--     | Wg.nil => Cs.nil
--     | Wg.cons x gt => wrap (k x) gt
--     | Wg.input k_gt => Cs.lam (fun x => wrap (k x) (k_gt x))

end Gen_trace


-- let's derive this as an existential from bisim
def to_cs (wg:Circuit') : Cs var := fun var =>
  open Circuit in
  match wg var with
  | nil => Circuit.nil
  | eq0 e wg => eq0 e (to_cs wg)
  | lam k => Cs.lam (fun x => to_cs (k x))
  --
  | Circuit.share e k =>
    Cs.lam (fun o =>
        Cs.eq0 (Exp.op e (Exp.v o)) (to_cs (k o)))
  | Circuit.is_zero e k =>
    Cs.lam (fun inv =>
      Cs.lam (fun o =>
        Cs.eq0 (Exp.op e (Exp.op (Exp.v o) (Exp.v inv))) (to_cs (k o))))

-- let's derive this as an existential from bisim
def to_cs {var:Type _} (wg:Circuit var) : Cs var :=
  match wg with
  | Circuit.nil => Cs.nil
  | Circuit.eq0 e wg => Cs.eq0 e (to_cs wg)
  | Circuit.lam k => Cs.lam (fun x => to_cs (k x))
  --
  | Circuit.share e k =>
    Cs.lam (fun o =>
        Cs.eq0 (Exp.op e (Exp.v o)) (to_cs (k o)))
  | Circuit.is_zero e k =>
    Cs.lam (fun inv =>
      Cs.lam (fun o =>
        Cs.eq0 (Exp.op e (Exp.op (Exp.v o) (Exp.v inv))) (to_cs (k o))))

def to_cs' (wg:Circuit') : Cs' := fun var => to_cs (wg var)

theorem soundness : ∀ (c:Circuit'), Functional.rw_bisim' c (to_cs' c) :=
  sorry

def completeness : ∀ (c:Circuit'),
  let c := c Felt;
  Functional.s_bisim c (Gen_trace.wrap (to_cs c) (Gen_trace.to_wg c)) := sorry


namespace Denotational

inductive Den where
  | bool : Option Unit -> Den
  | input : (Felt -> Den) -> Den

def eval (wg:Circuit Felt) : Den :=
  match wg with
  | Circuit.nil => Den.bool (some ())
  | Circuit.eq0 e wg =>
    if eval_e e = 0 then eval wg else Den.bool (none)
  | Circuit.lam k => Den.input (fun i => eval (k i))
  | Circuit.share e k => eval (k (eval_e e))
  | Circuit.is_zero e k =>
    if eval_e e = 0 then eval (k 1) else eval (k 0)

def eval' (wg:Circuit') : Den := eval (wg Felt)


inductive rw_bisim : (l r:Den) -> Prop where
  | bool
      (b:Option Unit)
      : rw_bisim (Den.bool b) (Den.bool b)
  | sync
      (kl:Felt -> Den)
      (kr:Felt -> Den)
      (hrec: ∀ x, rw_bisim (kl x) (kr x))
      : rw_bisim (Den.input kl) (Den.input kr)
  | async
      (h:Den)
      (kr:Felt -> Den)
      (x:Felt) -- ∃ x
      (hrec: rw_bisim h (kr x))
      : rw_bisim h (Den.input kr)

def rw_bisim' (h l : Circuit') : Prop := rw_bisim (eval' h) (eval' l)

end Denotational

end Phoas
