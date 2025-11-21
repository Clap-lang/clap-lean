import Lean
open Lean Meta Elab Tactic

syntax "crush" : tactic

def crushTactic : Tactic := fun _stx => do
  let goal ← getMainTarget
  match goal with
  | .app (.const ``Eq _) _ =>
    -- Goal is an equality
    evalTactic (← `(tactic| rfl))
  | .app (.const ``And _) _ =>
    -- Goal is a conjunction
    evalTactic (← `(tactic| constructor))
  | .app (.const ``Or _) _ =>
    -- Goal is a disjunction
    evalTactic (← `(tactic| first | left | right))
  | _ =>
    -- Default: try common tactics
    evalTactic (← `(tactic| first | assumption | rfl | trivial))
