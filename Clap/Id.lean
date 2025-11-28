import Clap.Circuit
import Clap.Simulation

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
  `wf cl cr -> cl ≈ (unwrap_e cr)`
-/

namespace Id

open Simulation

structure Entry (var1 var2:Type) where
  l : var1
  r : var2

inductive wf_e {var1 var2}: List (Entry var1 var2) -> Exp var1 -> Exp var2 -> Prop where
  | v : ∀ G x x', { l := x, r := x' } ∈ G   -- looks up in G
    -> wf_e G (.v x) (.v x')
  | c : ∀ G n, wf_e G (.c n) (.c n)
  | add : ∀ G e1 e2 e1' e2',
    wf_e G e1 e1' ->
    wf_e G e2 e2' ->
    wf_e G (.add e1 e2) (.add e1' e2')
  | mul : ∀ G e1 e2 e1' e2',
    wf_e G e1 e1' ->
    wf_e G e2 e2' ->
    wf_e G (.mul e1 e2) (.mul e1' e2')
  | sub : ∀ G e1 e2 e1' e2',
    wf_e G e1 e1' ->
    wf_e G e2 e2' ->
    wf_e G (.sub e1 e2) (.sub e1' e2')

inductive wf {var1 var2} : List (Entry var1 var2) -> Circuit var1 -> Circuit var2 -> Prop where
  | nil : ∀ G, wf G .nil .nil
  | eq0 : ∀ G el er cl cr,
      wf_e G el er ->
      wf G cl cr ->
      wf G (.eq0 el cl) (.eq0 er cr)
  | lam : ∀ G kl kr,
      (∀ el er, wf ({l := el, r := er}::G) (kl el) (kr er)) ->
      wf G (.lam kl) (.lam kr)
  | share : ∀ G el er kl kr,
      wf_e G el er ->
      (∀ xl xr, wf ({l := xl, r := xr}::G) (kl xl) (kr xr)) ->
      wf G (.share el kl) (.share er kr)
  | is_zero : ∀ G el er kl kr,
      wf_e G el er ->
      (∀ xl xr, wf ({l := xl, r := xr}::G) (kl xl) (kr xr)) ->
      wf G (.is_zero el kl) (.is_zero er kr)

-- TODO do we need to expose G ?
def wf' (c:Circuit') : Prop := ∀ var1 var2, wf [] (c var1) (c var2)

def add : Circuit' := fun _ =>
  .share (.c 1) (fun x =>
    .share (.c 2) (fun y =>
      .eq0 (.v x + .v y) .nil))

example : wf' add := by
  simp [wf',add]
  intros
  repeat (first | intros ; constructor | constructor | simp)

def unwrap_e {var} (e:Exp (Exp var)) : Exp var :=
  match e with
  | .v v => v
  | .c f => .c f
  | .add l r => .add (unwrap_e l) (unwrap_e r)
  | .mul l r => .mul (unwrap_e l) (unwrap_e r)
  | .sub l r => .sub (unwrap_e l) (unwrap_e r)

lemma unwrap_e_sem_pre : ∀ (el: Exp F) (er: Exp (Exp F)) G,
  wf_e G el er ->
   List.Forall (fun entry => entry.l = (Exp.eval entry.r)) G ->
   el ≈ (unwrap_e er)
:= by
  intros el
  induction el with
  | v =>
    intros er G wf FA
    cases wf
    case _ el er entry =>
    simp [unwrap_e]
    rw [List.forall_iff_forall_mem] at FA
    apply FA { l := el, r := er }
    assumption
  | c =>
    intros er G wf FA
    cases wf
    simp [unwrap_e]
  | add ll lr hl hr
  | mul ll lr hl hr
  | sub ll lr hl hr =>
    intros er G wf FA
    cases wf
    first | apply Exp.add_congr | apply Exp.mul_congr | apply Exp.sub_congr
    . apply hl
      repeat assumption
    . apply hr
      repeat assumption

def id {var} (c:Circuit (Exp var)) : Circuit var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 (unwrap_e e) (id c)
  | .lam k => .lam (fun x => id (k (.v x)))
  | .is_zero e k => .is_zero (unwrap_e e) (fun x => id (k (.v x)))
  | .share e k => .share (unwrap_e e) (fun x => id (k (.v x)))

def id' (c:Circuit') : Circuit' := fun var => id (c (Exp var))

theorem id_sem_pre : ∀ (cl: Circuit F) (cr:Circuit (Exp F)) G,
  wf G cl cr ->
   List.Forall (fun entry => entry.l = (Exp.eval entry.r)) G ->
   cl ≈ (id cr) := by
  intro cl
  induction cl with
  | nil =>
    intro cr G wf FA
    cases wf
    simp [id]
  | lam kl h =>
    intro cr G wf FA
    cases wf
    case _ kr wf =>
    apply lam_congr
    intro x
    apply h
    apply wf
    rw [List.forall_cons]
    simp [Exp.eval]
    assumption
  | eq0 el cl' h =>
    intro cr G wf FA
    cases wf
    case _ er cr' wf_e wf =>
    apply eq0_congr
    . apply unwrap_e_sem_pre
      repeat assumption
    . apply h
      repeat assumption
  | share el kl' h
  | is_zero el kl' h =>
    intro cr G wf FA
    cases wf
    case _ er kr' wf_e wf =>
    first | apply share_congr | apply is_zero_congr
    . apply unwrap_e_sem_pre
      repeat assumption
    . intro x
      apply h
      apply wf
      rw [List.forall_cons]
      simp [Exp.eval]
      assumption

end Id
