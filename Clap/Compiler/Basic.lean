import Mathlib.Data.ZMod.Basic

import Lean
import Qq

import Clap.Compilation
import Clap.Compiler.Deep

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

def curriedUserName (name : Name) (i : Nat) : Name :=
  name.appendBefore s!"curried{i}_"

def curriedUserNamesOfSize (name : Name) (n : Nat) : Array Name :=
  (Array.range n).map (curriedUserName name)

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

def curriedArgs (args : Array Expr) (p : Expr) : MetaM (Array FVar) := do
  let mut newFVars := #[]
  for arg in args do
    let userName ← arg.fvarId!.getUserName
    let (``Vector, #[_, sz]) := (← inferType arg).getAppFnArgs | continue
    let bi ← arg.fvarId!.getBinderInfo
    let names := curriedUserNamesOfSize userName sz.nat?.get!
    for name in names do
      newFVars := newFVars.push ⟨name, bi, ←mkAppM ``ZMod #[p]⟩
  return newFVars

def curriedBody (body : Expr) (newFVars : Array FVar) : TermElabM (LocalContext × LocalInstances × Expr) := do
  withLocalDecls (newFVars.map (·.toLocalDeclD)) fun _ ↦ do
    let lctx ← getLCtx
    let ictx ← getLocalInstances
    let res ← Meta.transform (skipConstInApp := true) body fun e ↦ do
      let_expr GetElem.getElem _ _ _ _ _ coll idx _ := e | return .continue
      let userName := curriedUserName (←coll.fvarId!.getUserName) idx.nat?.get!
      let .some fvar := lctx.findFromUserName? userName | throwError m!"Unknown local declaration: {userName}"
      return .done fvar.toExpr
    return (lctx, ictx, res)

def curry (p : Name) (f : Expr) : TermElabM Expr := do 
  lambdaTelescope f fun args body ↦ do
    let p ← fvarPrimeOfName p args
    let newFVars ← curriedArgs args p
    let (lctx, ictx, res) ← curriedBody body newFVars
    withLCtx lctx ictx do
      mkLambdaFVars (←lctx.getFVars.filterM fun fvar ↦ do return !(←inferType fvar).isAppOf ``Vector) res

def componentsOf (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let type ← inferType e
  let typeName := type.getAppFn.constName
  if !isStructure env typeName then throwError m!"{type} is not a structure."
  getStructureFields env typeName |>.mapM (mkProjection e)

def wg (circuitName : Name) (argFvars : Array Expr) : TermElabM Expr := do
  let #[(primeInst, p)] ← argFvars.filterMapM fun arg ↦ do
    let ⟨0, ~q(Fact (Nat.Prime $p)), _⟩ ← inferTypeQ arg | return .none
    return .some (arg, p)
    | throwError m!"Expecting a single instance of `Nat.Prime`."
  let args' ← argFvars.foldlM (init := #[]) fun acc arg ↦ do
    let t ← inferType arg
    let .some name := t.getAppFn.constName? | return acc
    if (←arg.fvarId!.getBinderInfo).isExplicit && isStructure (←getEnv) name
    then let components ← componentsOf arg
         return acc.append components
    else return acc
  let zmodType ← inferType <| ←args'[0]?.getDM (throwError m!"No explicit arguments found.")
  let args' ← mkAppM ``Array.mk #[←mkListLit zmodType args'.toList]
  let body ←
    mkAppM ``Wg.run #[
      ←mkAppM ``Clap.toWg' #[mkAppN (.const circuitName []) #[p, primeInst]], args'
    ]
  mkLambdaFVars argFvars body

def compile (p circuitName : Name) (f : Expr) : TermElabM Unit := do
  let compiledF ← serialise p f >>= curry p >>= toDeep
  let compiledFname := serialisedUserName circuitName
  addAndCompile <| .defnDecl {
    name        := compiledFname
    levelParams := []
    type        := ←inferType compiledF
    value       := compiledF
    hints       := .regular 18
    safety      := .safe
  }
  logInfo m!"Compiled {circuitName} into {compiledFname}."
  lambdaTelescope f fun args _ ↦ do
  let wg ← wg compiledFname args
  let wgName := compiledFname.appendAfter "_wg"
  addAndCompile <| .defnDecl {
    name        := wgName
    levelParams := []
    type        := ←inferType wg
    value       := wg
    hints       := .regular 18
    safety      := .safe
  }
  logInfo m!"Wg for {circuitName} is {wgName}."

elab "#compile" circuit:ident "using" p:ident : command => Command.liftTermElabM do
  let [decl] ← realizeGlobalConst circuit | throwError m!"Ambiguous constant: {circuit}"
  let .some decl := (←getEnv).find? decl | throwError m!"Undeclared constant: {circuit}"
  compile p.getId circuit.getId decl.value!

end Compiler

end Clap
