import Clap.Circuit
import Clap.Simulation
import Mathlib.Tactic

namespace Clap

/-
  This file introduces a trivial "optimization", the identity
  function, as an example of function that takes a circuit with an
  instantiation of the `var` type and returns a circuit with another
  instantiation. The same happens in the `unshare` optimization that
  takes a `Circuit (Exp var)` and returns a `Circuit var`.
  An important consequence is that we cannot define semantic
  preservation as `∀ c, eval c = eval (id c))` because `eval` and `id`
  take arguments of different type!
  Because of parametricity, we expect two circuits that have the same
  structure to behave similarly, after all if `var` remains abstract
  a circuit cannot change its behavior based on it.

  For this class of optimizations, we define semantic preservation as
  an equality between two distinct circuits, that are connected by a
  well-formed relation. Something along the lines of:
  `wf cl cr -> cl ≈ Exp.unwrap cr`
-/

def Exp.unwrap {p : ℕ} {var : Type} : Exp p (Exp p var) → Exp p var
  | .v val => val
  | .c f => .c f
  | .add l r => .add (unwrap l) (unwrap r)
  | .mul l r => .mul (unwrap l) (unwrap r)
  | .sub l r => .sub (unwrap l) (unwrap r)

open Simulation

variable {p : ℕ} {var : Type}

abbrev Entry := Prod

inductive Exp.wf {var₁ var₂ : Type} (G : Set (Entry var₁ var₂)) : Exp p var₁ → Exp p var₂ → Prop where
  | v {x x'} :
    (x, x') ∈ G → -- looks up in G
    wf G (.v x) (.v x')
  | c {x} :
    wf G (.c x) (.c x)
  | add {e₁ e₂ e₁' e₂'} :
    wf G e₁ e₁' →
    wf G e₂ e₂' →
    wf G (.add e₁ e₂) (.add e₁' e₂')
  | mul {e₁ e₂ e₁' e₂'} :
    wf G e₁ e₁' →
    wf G e₂ e₂' →
    wf G (.mul e₁ e₂) (.mul e₁' e₂')
  | sub {e1 e2 e1' e2'} :
    wf G e1 e1' →
    wf G e2 e2' →
    wf G (.sub e1 e2) (.sub e1' e2')

inductive Circuit.wf {var₁ var₂ : Type} : Set (Entry var₁ var₂) → Circuit p var₁ → Circuit p var₂ → Prop where
  | nil {G} :
    wf G .nil .nil
  | eq0 {G el er cl cr} :
    Exp.wf G el er →
    wf G cl cr →
    wf G (.eq0 el cl) (.eq0 er cr)
  | lam {G kl kr} :
    (∀ el er, wf ({(el, er)} ∪ G) (kl el) (kr er)) →
    wf G (.lam kl) (.lam kr)
  | share {G el er kl kr} :
    Exp.wf G el er →
    (∀ xl xr, wf ({(xl, xr)} ∪ G) (kl xl) (kr xr)) →
    wf G (.share el kl) (.share er kr)
  | is_zero {G el er kl kr} :
    Exp.wf G el er →
    (∀ xl xr, wf ({(xl, xr)} ∪ G) (kl xl) (kr xr)) →
    wf G (.is_zero el kl) (.is_zero er kr)

-- TODO do we need to expose G ?
def wf' (c : Circuit p var) : Prop := Circuit.wf {} c c

namespace Example

def add {var} : Circuit 7 var :=
  .share (.c 1) (fun x =>
    .share (.c 2) (fun y =>
      .eq0 (.v x + .v y) .nil))

example {var} : wf' (var := var) add := by
  aesop (add simp [wf', add]) (add safe (by constructor))

end Example

lemma unwrap_e_sem_pre {el : Expₑ p} {er: Exp p (Expₑ p)} {G}
  (h₁ : Exp.wf G el er)
  (h₂ : ∀ entry ∈ G, entry.1 = entry.2.eval) :
  el ≈ er.unwrap
:= by
  induction' el with var X l r l r l e generalizing er <;> cases h₁ <;>
  aesop (add safe (by
    first
    | apply Exp.add_congr
    | apply Exp.mul_congr
    | apply Exp.sub_congr)
  )

def id {var} : Circuit p (Exp p var) → Circuit p var
  | .nil => .nil
  | .eq0 e c => .eq0 e.unwrap (id c)
  | .lam k => .lam fun x ↦ id (k (.v x))
  | .is_zero e k => .is_zero e.unwrap fun x ↦ id (k (.v x))
  | .share e k => .share e.unwrap fun x ↦ id (k (.v x))
  | .assert_range w e c => .assert_range w e.unwrap (id c)

-- def id' (c:Circuit' F) : Circuit' F := fun var => id (c (Exp F var))

  -- | nil
  -- | eq0 (e : Exp p var) (c : Circuit p var)
  -- | lam (cont : var → Circuit p var)
  -- | share (e : Exp p var) (cont : var → Circuit p var)
  -- | is_zero (e : Exp p var) (cont : var → Circuit p var)
  -- | assert_range (w : ℕ) (e : Exp p var) (c : Circuit p var)
  -- | div_rem (e : Exp p var) (cont : var × var → Circuit p var)

section

attribute [local grind =] Exp.eval

open Circuit in
theorem id_sem_pre {cl : Circuitₑ p} {cr : Circuit p (Expₑ p)} {G}
  (h₁ : Circuit.wf G cl cr)
  (h₂ : ∀ entry ∈ G, entry.1 = entry.2.eval) :
  cl ≈ id cr := by
  induction' cl with e c cont e cont e cont w e c e cont generalizing G cr <;> rcases h₁
  · rfl
  · exact eq0_congr (unwrap_e_sem_pre ‹_› ‹_›) (cont ‹_› ‹_›)
  next _ wf => exact lam_congr fun _ ↦ cont _ (wf _ _) (by grind)
  next _ wf => exact share_congr (unwrap_e_sem_pre ‹_› ‹_›) (fun _ ↦ w _ (wf _ _) (by grind))
  next _ wf => exact is_zero_congr (unwrap_e_sem_pre ‹_› ‹_›) (fun _ ↦ e _ (wf _ _) (by grind))

end

end Clap
