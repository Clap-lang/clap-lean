import Lean
import Lean.Meta.Sym.SymM

open Lean Meta Elab

namespace Clap.Compiler

namespace Simp

opaque SimpWrap {α : Type} : α → Prop

def withSimpableExpression {m} [Monad m] [MonadLiftT MetaM m]
                           (e : Expr) (f : Expr → m Expr) : m Expr := do
  let_expr SimpWrap _ result := ← f (←mkAppM ``SimpWrap #[e]) | unreachable!
  return result

/--
TODO: Generalise for k-goals-producing tactics.
-/
def _root_.Lean.Expr.runTactic {m}
                               [Monad m] [MonadLiftT MetaM m]
                               [MonadError m] [MonadMCtx m]
                               (e : Expr) (stx : Syntax) : m Expr := do
  withSimpableExpression e fun e ↦ do
    let mvar ← mkFreshExprMVar (.some e) MetavarKind.syntheticOpaque
    let ([mvar], _) ←
      Elab.runTactic mvar.mvarId! stx {} {} | -- TODO: Check if we need `(←read)` and `(←get)` for `runTactic`
        throwError "{stx} generated more than a single goal on:\n{e}"
    instantiateMVars (←mvar.getType)

/-
`simp` is inconvenient to call from `MetaM` (viz. `mkSimpConfig`).
As such, we simply interface with it via a `runTactic` and construct the 'appropriate' syntax.
-/
namespace API

inductive Order where | Pre | Post

instance : Repr Order where
  reprPrec x _ := match x with | .Pre => f!"Pre" | .Post => f!"Post"

inductive Lemma where
  | pos (name : Name) (order : Order)
  | neg (name : Name)

structure SimpSet where
  pos : Array (Name × Order) := #[]
  neg : Array Name := #[]
deriving Repr

def SimpSet.withAllPost (pos neg : Array Name := #[]) : SimpSet
  where pos := pos.map (·, .Post)
        neg := neg

def SimpSet.toSimpSet (s : SimpSet) : Array Lemma :=
  s.pos.map (Function.uncurry Lemma.pos) ++
  s.neg.map Lemma.neg

def SimpSet.union (s₁ s₂ : SimpSet) : SimpSet where
  pos := s₁.pos ++ s₂.pos
  neg := s₁.neg ++ s₂.neg

-- open Sym.Simp in
-- public def mkSimprocFor (declNames : Array Name) (d : Discharger := dischargeNone) : MetaM Simproc := do
--   let mut thms : Theorems := {}
--   for declName in declNames do
--     thms := thms.insert (← mkTheoremFromDecl declName)
--   return thms.rewrite d

-- def mkAlternativeSimprocFor (name : Name) : MetaM Sym.Simp.Simproc := do
--   let thm := Sym.Simp.mkTheoremFromDecl name
--   _

def simproc? (name : Name) : MetaM (Option ConstantInfo) := do
  let .some ci := (←getEnv).find? name | throwError m!"Undeclared constant: {name}"
  return if ci.type.isConstOf `Lean.Meta.Sym.Simp.Simproc
         then .some ci
         else .none

def isSimproc (name : Name) : MetaM Bool := return (←simproc? name).isSome

def getSimproc (name : Name) : MetaM Sym.Simp.Simproc := do
  discard (isSimproc name)
  let .ok sproc := unsafe (←getEnv).evalConst Sym.Simp.Simproc {} name
    | throwError m!"Failed to evaluate: {name}"
  return sproc

def orElse (names : Array Name) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  return simprocs.foldl (· <|> ·) (fun _ ↦ return .rfl) -- I hope this is the `.continue`...

def andThen (names : Array Name) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  return simprocs.foldl (· >> ·) (fun _ ↦ return .rfl) -- I hope this is the `.continue`...

instance : Singleton Sym.Simp.Simproc Sym.Simp.Methods where
  singleton x := {post := x}

instance : Union Sym.Simp.Methods := ⟨
  fun m₁ m₂ =>
    {
      pre := m₁.pre >> m₂.pre
      post := m₁.post >> m₂.post
    }
  ⟩

def SimpSet.toMethods (s : SimpSet) : Sym.SymM Sym.Simp.Methods := do
  unless s.neg.isEmpty do throwError m!"Erasing Sym.simp theorems currently unsupported."
  let (pre, post) := (s.pos.partition fun (_, order) ↦ order matches .Pre).map (·.map Prod.fst) (·.map Prod.fst)
  let (preSimp, preThm) ← pre.toList.partitionM (liftM ∘ isSimproc)
  let (postSimp, postThm) ← post.toList.partitionM (liftM ∘ isSimproc)
  logInfo m!"preThm: {preThm}\npreSimp: {preSimp}\npostThm:{postThm}\npostSimp:{postSimp}"
  let simprocsPre := (←Sym.mkSimprocFor preThm.toArray) <|> (←andThen preSimp.toArray)
  let simprocsPost := (← Sym.mkSimprocFor postThm.toArray) <|> (←andThen postSimp.toArray)
  return {
    pre := simprocsPre
    post := simprocsPost
  }

def config : Sym.Simp.Config :=
  {
    maxSteps := 1_000_000
  }

instance : Union SimpSet := ⟨SimpSet.union⟩

instance : Singleton Name SimpSet where
  singleton x := ⟨#[(x, .Post)], #[]⟩

section

open Parser Tactic

set_option hygiene false in
def configStx (singlePass : Bool := false) : Sym.Simp.SimpM (TSyntax ``optConfig) := do
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
  Sym.Simp.SimpM (Syntax.TSepArray [``simpStar, ``simpErase, ``simpLemma] ",") := do
  let arrStx ← sets.mapM fun lemma ↦
    match lemma with
    | .neg name => `(simpErase|-$(mkIdent name):term)
    | .pos name .Post => `(simpLemma|$(mkIdent name):term)
    | .pos name .Pre => `(simpLemma|↓$(mkIdent name):term)
  return Syntax.TSepArray.ofElems arrStx

end
end API

open API

set_option hygiene false in
def mkSimp (simpset : SimpSet)
           (only singlePass : Bool := false) : Sym.Simp.SimpM (TSyntax `tactic) := do
  let simpsetStx ← simpSetStx simpset.toSimpSet
  if only
  then `(tactic| simp $(←configStx singlePass) only [$[$simpsetStx],*])
  else `(tactic| simp $(←configStx singlePass) [$[$simpsetStx],*])

def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : Nat) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats * 1000})

set_option hygiene false in
def simplify (simpset : Sym.Simp.Methods) (e : Expr) (only singlePass : Bool := false) : Sym.Simp.SimpM Expr := do
  -- tryCatchRuntimeEx
    -- (forceHeartbeats 300_000 do
      lambdaTelescope e fun args body ↦ do
        logInfo m!"Calling Sym.simp on:\n{body}"
        let res ← Sym.simp body simpset config
        logInfo m!"Result:\n{res.getResultExpr body}"
        Sym.mkLambdaFVarsS args (res.getResultExpr body)
    -- )
    -- (fun _ ↦ do throwError s!"Simp Timeout:\n{←PrettyPrinter.ppExpr e}")

end Simp

end Clap.Compiler
