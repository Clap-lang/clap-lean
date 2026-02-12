import Mathlib.Data.ZMod.Basic

import Lean
import Qq

namespace Clap

open Lean Qq Elab Meta

/--
TODO: Can a projection here have more than 1 arg of the appropriate type?
-/
def _root_.Lean.Expr.projecteeOfType (e : Expr) (type : Name) : MetaM Name := do
  let #[arg] ← e.getAppArgs.filterM fun e ↦ do
    return (←Meta.inferType e).getAppFn.constName! == type
    | throwError m!"Logic error - projecting from: {e}."
  arg.fvarId!.getUserName

namespace Compiler


structure FVar where
  userName   : Name
  bi         : BinderInfo
  nondepType : Expr
  deriving BEq

namespace FVar

def toLocalDeclD (fvar : FVar) : Name × BinderInfo × (Array Expr → TermElabM Expr) :=
  (fvar.userName, fvar.bi, fun _ ↦ return fvar.nondepType)

def toLocalDecl (fvar : FVar) : Name × BinderInfo × TermElabM Expr :=
  (fvar.userName, fvar.bi, return fvar.nondepType)

end FVar

def fvarPrimeOfName (p : Name) (args : Array Expr) : MetaM Expr := do
  let .some p ← args.findM? fun arg ↦ do return (←arg.fvarId!.getUserName) == p
    | throwError m!"{p} not found."
  return p

def serialisedUserName (name : Name) : Name := name.appendAfter "_ser"

def vectorTypeOfSerialisable (prime : Q(Nat)) (sz : Nat) : Expr :=
  mkApp2 (.const `Vector [.zero]) q(ZMod $prime) (ToExpr.toExpr sz)

def getElemVectorOfIdx (coll : Expr) (idx : Nat) : TermElabM Expr := do
  let_expr Vector _ sz := ← Meta.inferType coll | throwError m!"{coll} must be a Vector."
  let idxQ : Q(Nat) := ToExpr.toExpr idx
  let szQ : Q(Nat) := sz
  let getElemSansProof ← Meta.mkAppM ``GetElem.getElem #[coll, ToExpr.toExpr idx]
  let proof ← Elab.Term.mkTacticMVar q($idxQ < $szQ) (←`(by get_elem_tactic)) .term
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars <| mkAppN getElemSansProof #[proof]

def serialisedArgs (args : Array Expr) (p : Expr) :
  MetaM (Array FVar × Std.HashSet Expr × Std.HashSet Name) := do
  let env ← getEnv
  let mut newFVars := #[]
  let mut serialisableFVars : Std.HashSet Expr := ∅
  let mut toSerialise : Std.HashSet Name := ∅
  for arg in args do
    let userName ← arg.fvarId!.getUserName
    let typeName := (←Meta.inferType arg).getAppFn.constName
    if isStructure env typeName && !(←arg.fvarId!.getBinderInfo).isInstImplicit
    then let bi ← arg.fvarId!.getBinderInfo
         let size := getStructureFields env typeName |>.size
         newFVars := newFVars.push ⟨serialisedUserName userName, bi, vectorTypeOfSerialisable p size⟩
         serialisableFVars := serialisableFVars.insert arg
         toSerialise := toSerialise.insert typeName
  return (newFVars, serialisableFVars, toSerialise)

def serialisedBody (body : Expr) (newFVars : Array FVar) (toSerialise : Std.HashSet Name) :
  TermElabM (LocalContext × LocalInstances × Expr) :=
  withLocalDecls (newFVars.map (·.toLocalDeclD)) fun _ ↦ do
    let lctx ← getLCtx
    let ictx ← getLocalInstances
    let res ← Meta.transform (skipConstInApp := true) body fun e ↦ do
      let (name, _) := e.getAppFnArgs
      match (←getEnv).getProjectionStructureName? name with
      | .none => return .continue
      | .some val =>
        if toSerialise.contains val
        then let projectee ← serialisedUserName <$> e.projecteeOfType val
             let serialisedIdx := (←getProjectionFnInfo? name).get!.i
             let fvar := lctx.findFromUserName? projectee |>.get!.toExpr
             let vectorAccess ← getElemVectorOfIdx fvar serialisedIdx
             return .done vectorAccess
        return .continue
    return (lctx, ictx, res)

def serialise (p : Name) (f : Expr) : TermElabM Expr := do
  lambdaTelescope f fun args body ↦ do
    let p ← fvarPrimeOfName p args
    /-
    Synthesise all `FVar`s first to preserve 'the' `Meta.transform` invariant.

    We need both serialisable _and_ their serialised counterpart in the context
    while we synthesize the transformed expression.
    -/
    let (newFVars, serialisableFVars, toSerialise) ← serialisedArgs args p
    let (lctx, ictx, res) ← serialisedBody body newFVars toSerialise
    withLCtx lctx ictx do
      mkLambdaFVars (lctx.getFVars.filter (!serialisableFVars.contains ·)) res

end Compiler

end Clap
