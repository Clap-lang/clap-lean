import Lean
import Qq

import Clap.Simulation

open Lean Qq

namespace Clap

def accept : Unit -> Unit := fun () => ()

def lhsOfBisim (conclusion : Expr) : MetaM Expr := do
  let e ← instantiateMVarsQ (α := q(Prop)) conclusion
  match e with
  | ~q(Simulation.s_bisim $lhsQ _) => pure lhsQ
  | _ => throwError "{e} is not `Simulation.s_bisim."

def simulationExprs : Array (Name × Name) := #[
  (`Clap.circuit_ext, `id)
]

variable {F:Type} [Field F] [DecidableEq F]

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (hint : g' = Circuit.lam g)
  (h: Simulation.s_bisim f (Circuit.eval (Circuit.lam g))) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

def step (proof witness : MVarId) (rest : List MVarId) (lhs : Expr) : MetaM (List MVarId) := do
  match lhs with
  | .lam .. =>
    let (proofGoals, _) ← proof.withContext do
      Elab.runTactic proof (Unhygienic.run `(tactic|apply circuit_ext (h := Simulation.s_bisim.lam _ _ fun h ↦ ?rest)))
    let (witnessGoals, _) ← witness.withContext do
      Elab.runTactic witness (Unhygienic.run `(tactic|refine Circuit.lam fun _ ↦ ?y))
    return proofGoals.getLast! :: witnessGoals ++ proofGoals.take (proofGoals.length - 1) ++ rest
  | e@(.app ..) =>
    let ⟨1, ~q(Option Unit), e⟩ ← inferTypeQ e | return rest
    let ~q(Option.some (accept ())) := e | return rest
    let (proofGoals, _) ← proof.withContext do
      Elab.runTactic proof (Unhygienic.run `(tactic|apply $(mkIdent `abc)))
    return proofGoals ++ [witness] ++ rest
  | _ => logInfo m!"didn't match"; return [proof]

open Expr in
def extractTac (goal witness : MVarId) (rest : List MVarId) : MetaM (List MVarId) := do
  let conclusion ← goal.getType
  let lhs ← lhsOfBisim conclusion
  step goal witness rest lhs

open Elab Tactic in
elab "extract" : tactic => do
  let (proof :: witness :: rest) ← getUnsolvedGoals | throwError "Expected two goals; proof and witness."
  extractTac proof witness rest >>= setGoals

section EXAMPLES

def ex (i: F) : Option Unit := do
--  eq0 i
  accept ()

lemma abc :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor

def extract_automatic :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  unfold ex
  refine ⟨?c,?p⟩
  swap
  repeat extract
  swap
  rfl

#print extract_automatic

def extract_manual :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  unfold ex
  refine ⟨?c,?p⟩
  -- iterate 2
  -- first
  case' p => -- case' does not enforce to close the goal
    apply circuit_ext (h := Simulation.s_bisim.lam _ _ (fun h ↦ ?rest))
  skip
  case' c =>
    refine Circuit.lam fun _ ↦ ?y
  case' rest =>
    apply abc
  skip
  swap
  rfl

end EXAMPLES

end Clap
