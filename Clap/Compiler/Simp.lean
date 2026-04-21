import Lean

open Lean Meta Elab

namespace Clap.Compiler

namespace Simp

private opaque SimpWrap {α : Type} : α → Prop

/-
`simp` is inconvenient to call from `MetaM` (viz. `mkSimpConfig`).
As such, we simply interface with it via a `runTactic` and construct the 'appropriate' syntax.
-/
namespace API

inductive Lemma where
  | pos (name : Name) (isPre : Bool)
  | neg (name : Name)

structure SimpSet where
  pos : Array (Name × Bool) := #[]
  neg : Array Name := #[]
deriving Repr

def SimpSet.withAllPost (pos neg : Array Name := #[]) : SimpSet
  where pos := pos.map (·, true)
        neg := neg

def SimpSet.toSimpSet (s : SimpSet) : Array Lemma :=
  s.pos.map (Function.uncurry Lemma.pos) ++
  s.neg.map Lemma.neg

def SimpSet.union (s₁ s₂ : SimpSet) : SimpSet where
  pos := s₁.pos ++ s₂.pos
  neg := s₁.neg ++ s₂.neg

section

open Parser Tactic

set_option hygiene false in
def configStx (singlePass : Bool := false) : MetaM (TSyntax ``optConfig) := do
  `(optConfig|(
      config := {
        failIfUnchanged := false
        arith           := true
        singlePass      := $(if singlePass then mkIdent `true else mkIdent `false)
        maxSteps        := $(Syntax.mkNatLit defaultMaxSteps)
      }
  ))
  where defaultMaxSteps := 10_000_000

def simpSetStx (sets : Array Lemma) :
  MetaM (Syntax.TSepArray [``simpStar, ``simpErase, ``simpLemma] ",") := do
  let arrStx ← sets.mapM fun lemma ↦
    match lemma with
    | .neg name => `(simpErase|-$(mkIdent name):term)
    | .pos name true => `(simpLemma|$(mkIdent name):term)
    | .pos name false => `(simpLemma|↓$(mkIdent name):term)
  return Syntax.TSepArray.ofElems arrStx

end
end API

open API

set_option hygiene false in
def mkSimp (simpset : SimpSet)
           (only singlePass : Bool := false) : TermElabM (TSyntax `tactic) := do
  let simpsetStx ← simpSetStx simpset.toSimpSet
  if only
  then `(tactic| simp $(←configStx singlePass) only [$[$simpsetStx],*])
  else `(tactic| simp $(←configStx singlePass) [$[$simpsetStx],*])

set_option hygiene false in
def simplify (simpset : SimpSet) (e : Expr) (only singlePass : Bool := false) : TermElabM Expr := do
  lambdaTelescope e fun args body ↦ do
    let abc ← mkAppM ``SimpWrap #[body]
    let mvar ← mkFreshExprMVar (.some abc) MetavarKind.syntheticOpaque
    let ([mvar], _) ←
      Elab.runTactic mvar.mvarId! (←mkSimp simpset only singlePass) (←read) (←get) |
        throwError "Simp generated more than a single goal on:\n{e}"
    let_expr SimpWrap _ x := ←instantiateMVars (←mvar.getType) | unreachable!
    mkLambdaFVars args x
  where simpAll := `simpAll

end Simp

end Clap.Compiler
