import Clap.Circuit
import Clap.Simulation

namespace Clap

variable (F var:Type) [Field F] [DecidableEq F]

def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

def share (e:F) : F := e

def is_zero (e:F) : F := if e = 0 then 1 else 0

def accept : Unit -> Unit := fun () => ()

/-
  A circuit is a function from any number of F arguments to Option Unit.
-/

def ex (i:F) : Option Unit := do
  eq0 F i
  let vi <- share F i
  eq0 F (vi + i)
  accept ()

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun : Circuit' F := fun _ =>
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .nil))))

lemma equiv_eq0 : ∀ (el:F) (er:Exp F F) (cl:Option Unit) (cr:Circuit F F),
  el = Exp.eval er ->
  Simulation.s_bisim cl (Circuit.eval cr) ->
  Simulation.s_bisim (Option.bind (eq0 F el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  intro el er cl cr he hc
  simp only [Circuit.eval,Option.bind,eq0]
  split
  split
  case _ _ heq her =>
    rw [her] at he
    rw [he] at heq
    simp at heq
  case _ _ hel her =>
    constructor
  case _ _ _ hel =>
    simp at hel
    rw [he] at hel
    simp
    split
    . apply hc
    . contradiction

lemma equiv_share : ∀ (el:F) (er:Exp F F) (kl:F -> Option Unit) (kr:F -> Circuit F F),
  el = Exp.eval er ->
  (∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) ->
  Simulation.s_bisim (bind (share F el) kl) (Circuit.eval (.share er kr)) := by
  intro el er kl kr he hk
  simp only [Circuit.eval,bind,share]
  rw [he]
  apply hk

theorem equiv : Simulation.s_bisim (ex F) (Circuit.eval' (ex_circuit_fun F)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  constructor
  intro x
  apply equiv_eq0
  simp [Exp.eval]
  apply equiv_share
  simp [Exp.eval]
  intro
  apply equiv_eq0
  simp [Exp.eval]
  constructor

end Clap
