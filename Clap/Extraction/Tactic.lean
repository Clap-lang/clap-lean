import Lean
import Qq

import Clap.Simulation

open Lean Qq

namespace Clap

def accept : Unit -> Unit := fun () => ()

open Expr in
def extractTac (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let conclusion ← goal.getType
  logInfo m!"Conclusion: {conclusion} IsAppOf: {conclusion.appFn!}"
  let_expr Simulation.s_bisim _ _ lhsE _ := conclusion |
    throwError m!"{conclusion} must be of the shape `Simulation.s_bisim lhs rhs`."
  match lhsE with
  | .lam binder t body _ => logInfo m!"Is lambda."
  | _ => logInfo m!"NOT lambda."
  logInfo m!"lhsE = {lhsE}\nAs expr = {repr lhsE}"
  return goal

  -- let conclusion : Q(Prop) ← goal.getType
  -- let ~q(Simulation.s_bisim $lhsQ _) := conclusion |
  --   throwError m!"{conclusion} must be of the shape `Simulation.s_bisim lhs rhs`."
  -- logInfo m!"got: {repr lhsQ}\n got: {lhsQ}"
  -- match ← inferTypeQ lhsQ with
  -- | ⟨1, ~q(Option Unit), ~q(some (accept ()))⟩ => logInfo m!"some (accept ()) : Option Unit"; return goal
  -- | ⟨2, ~q((_ : Type) → (Option.{0} Unit)), _⟩ => logInfo m!"FUNKTION DESU"; return goal
  -- | _ => logInfo m!"WELL OOOPS :("; return goal

elab "extract" : tactic => Elab.Tactic.liftMetaTactic1 extractTac

section EXAMPLE

variable {F:Type} [Field F] [DecidableEq F]

def ex (i: F) : Option Unit := do
--  eq0 i
  accept ()

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (hint : g' = Circuit.lam g)
  (h: Simulation.s_bisim f (Circuit.eval (Circuit.lam g))) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

lemma abc :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor
-- -- set_option pp.universes true in
-- def extract' :
--   { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
--   unfold ex
--   refine ⟨?c,?p⟩
--   -- iterate 2
--   -- first
--   case' p => -- case' does not enforce to close the goal
--     extract
--     apply circuit_ext (h := ?rest)
--   case' c =>
--     refine Circuit.lam fun _ ↦ ?y
--   case' rest =>

--     constructor
--     intros x
--     extract

--     apply abc
--   swap
--   rfl


def extract' :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  unfold ex
  refine ⟨?c,?p⟩
  -- iterate 2
  -- first
  case' p => -- case' does not enforce to close the goal
    apply circuit_ext (h := ?rest)
  case' c =>
    refine Circuit.lam fun _ ↦ ?y
  case' rest =>
    constructor
    intros x
    apply abc
  swap
  rfl

end EXAMPLE

end Clap
