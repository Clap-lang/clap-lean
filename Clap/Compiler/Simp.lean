import Lean

open Lean Meta Elab

namespace Clap.Compiler

namespace Simp

private opaque SimpWrap {α : Type} : α → Prop

set_option hygiene false in
def simpOpen : TermElabM (TSyntax `tactic) :=
  `(tactic|
    simp (
      config := {
        failIfUnchanged     := false
        arith               := true
        singlePass          := true

        autoUnfold          := false
        unfoldPartialApp    := false

        maxSteps            := 10000000
    }))

set_option hygiene false in
def mkSimpSet (simpset : Name) : TermElabM (TSyntax `tactic) :=
  let simpset : Ident := mkIdent simpset
  `(tactic|
    simp (
      config := {
        failIfUnchanged     := false
        arith               := true
        singlePass          := true

        autoUnfold          := false
        unfoldPartialApp    := false

        maxSteps            := 10000000
    }) only [$simpset:ident])

set_option hygiene false in
def simplify (simpSet : Name) (e : Expr) : TermElabM Expr := do
  lambdaTelescope e fun args body ↦ do
    let abc ← mkAppM ``SimpWrap #[body]
    let mvar ← mkFreshExprMVar (.some abc) MetavarKind.syntheticOpaque
    let simp := if simpSet == simpAll then simpOpen else mkSimpSet simpSet
    let ([mvar], _) ←
      Elab.runTactic mvar.mvarId! (←simp) (←read) (←get) |
        throwError "Simp generated more than a single goal on:\n{e}"
    let_expr SimpWrap _ x := ←instantiateMVars (←mvar.getType) | unreachable!
    mkLambdaFVars args x
  where simpAll := `simpAll

end Simp

end Clap.Compiler
