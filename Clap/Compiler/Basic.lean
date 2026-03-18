import Mathlib.Data.ZMod.Basic

import Lean
import Qq

import Clap.Compilation
import Clap.Compiler.Deep
import Clap.Lang
import Clap.Compiler.Reduce

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

def serialisedUserName (name : Name) : Name := name.appendAfter "_circuit"

def curriedUserName (name : Name) (i : Nat) : Name :=
  name.appendBefore s!"curried{i}_"

def curriedUserNamesOfSize (name : Name) (n : Nat) : Array Name :=
  (Array.range n).map (curriedUserName name)

def vectorTypeOfSerialisable (prime : Name) (sz : Nat) : Expr :=
  mkApp2 (.const `Vector [.zero]) (.app (.const `ZMod []) (.const prime [])) (ToExpr.toExpr sz)

def getElemVectorOfIdx (coll : Expr) (idx : Nat) : TermElabM Expr := do
  let_expr Vector _ sz := ← Meta.inferType coll | throwError m!"{coll} must be a Vector."
  let idxQ : Q(Nat) := ToExpr.toExpr idx
  let szQ : Q(Nat) := sz
  let getElemSansProof ← Meta.mkAppM ``GetElem.getElem #[coll, ToExpr.toExpr idx]
  let proof ← Elab.Term.mkTacticMVar q($idxQ < $szQ) (←`(by get_elem_tactic)) .term
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars <| mkAppN getElemSansProof #[proof]

def withTransformedArgs.{u}
  {n : Type → Type u} [MonadControlT MetaM n] [Monad n] {α : Type} [Inhabited α]
  (args : Array Expr)
  (f : Expr → n (Option (Array (Name × Expr)))) (k : Array Expr → n α) : n α := do
  withLocalDeclsDND (←Array.flatten <$> args.filterMapM f) k

def isPrivileged (p : Q(ℕ)) (e : Expr) : TermElabM Bool := do
  let type ← inferType e
  return type.isAppOf ``Vector || (←isDefEq type q(ZMod $p))

def serialisedLam (body : Expr) : TermElabM Expr := do
  Meta.transform (skipConstInApp := true) body fun e ↦ do
    let env ← getEnv
    let (name, _) := e.getAppFnArgs
    match env.getProjectionStructureName? name with
    | .none => return .continue
    | .some val =>
      if isClass env val || e.isAppOf ``Vector.toArray then return .continue
      let projectee ← serialisedUserName <$> e.projecteeOfType val
      let fvar := (←getLCtx).findFromUserName? projectee |>.get!.toExpr
      let serialisedIdx := (←getProjectionFnInfo? name).get!.i
      .done <$> getElemVectorOfIdx fvar serialisedIdx

def isSerialisableType (typeName : Name) : MetaM Bool := do
  return isStructure (←getEnv) typeName && !isClass (←getEnv) typeName

def serialiseArg (prime : Name) (arg : Expr) : TermElabM (Option (Array (Name × Expr))) := do
  let fvar := arg.fvarId!
  let typeName := (←Meta.inferType arg).getAppFn.constName
  let env ← getEnv
  if (←isSerialisableType typeName) && !(←isPrivileged (.const prime []) arg)
  then let size := getStructureFields env typeName |>.size
       return .some #[(
         serialisedUserName (←fvar.getUserName),
         vectorTypeOfSerialisable prime size
       )]
  else return .none

def serialise (prime : Name) (f : Expr) : TermElabM Expr := do
  lambdaTelescope f fun args body ↦ do
    withTransformedArgs args (serialiseArg prime) fun _ ↦ do
      mkLambdaFVars (usedOnly := true) (←getLCtx).getFVars (←serialisedLam body)

def curryArg (prime : Name) (arg : Expr) : MetaM (Option (Array (Name × Expr))) := do
  let userName ← arg.fvarId!.getUserName
  let (``Vector, #[_, sz]) := (← inferType arg).getAppFnArgs | return .none
  let names := curriedUserNamesOfSize userName sz.nat?.get!
  let type ← mkAppM ``ZMod #[.const prime []]
  return .some (Array.zip names (Array.replicate names.size type))

def curriedBody (body : Expr) : TermElabM (LocalContext × LocalInstances × Expr) := do
  let lctx ← getLCtx
  let ictx ← getLocalInstances
  -- Replace every `x` with `#[x_0, ...]`.
  let res ← Meta.transform (skipConstInApp := true) body
    (pre := fun e ↦ do
      if e.isFVar
      then -- TODO: Refactor, reuses `curriedArgs`.
        let (``Vector, #[t, sz]) := (←inferType e).getAppFnArgs | return .continue
        let names := curriedUserNamesOfSize (←e.fvarId!.getUserName) sz.nat?.get!
        let array ← mkAppM ``Array.mk #[
          ←mkListLit t (←names.mapM (return lctx.findFromUserName? · |>.get!.toExpr)).toList
        ]
        let vecSansProof := mkAppN (.const ``Vector.mk [.zero]) #[t, sz, array]
        let Expr.forallE _ t _ _ ← inferType vecSansProof | throwError "Expected function type."
        let vec := Expr.app vecSansProof (←mkEqRefl t)
        return .done vec
      else return .continue)
    (post := fun e ↦ do
      if e.isAppOf ``GetElem.getElem
      then return .done (←Meta.reduce e) -- TODO: Do we need to be more specific than reduce?
      else return .continue)
  return (lctx, ictx, res)

/--
TODO: Needs the same refactor as serialise (using `withTransformedArgs`, etc.).
      Currently, `curry` is ugly.
-/
def curry (prime : Name) (f : Expr) : TermElabM Expr := do
  lambdaTelescope f fun args body ↦ do
    withTransformedArgs args (liftM ∘ curryArg prime) fun _ ↦ do
      let (lctx, _, res) ← curriedBody body
      mkLambdaFVars (←lctx.getFVars.filterM fun fvar ↦ do return !(←inferType fvar).isAppOf ``Vector)
                    res

def componentsOf (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let type ← inferType e
  let typeName := type.getAppFn.constName
  if !isStructure env typeName then throwError m!"{type} is not a structure."
  getStructureFields env typeName |>.mapM (mkProjection e)

/--
TODO: Needs refactor. Shares with `curry/serialise`.
-/
def wg (p : Name) (argFvars : Array Expr) : TermElabM Expr := do
  let args' ← argFvars.foldlM (init := #[]) fun acc arg ↦ do
    let t ← inferType arg
    let .some name := t.getAppFn.constName? | return acc
    -- TODO: This handling is temporary. We'll be splitting on public/private inputs at some point.
    if (←arg.fvarId!.getBinderInfo).isExplicit
    then if ←isDefEq t.getAppFn (.const ``Vector [.zero])
         then -- TODO: Refactor, reuses `curriedBody`.
              let (``Vector, #[_, sz]) := t.getAppFnArgs | return acc
              let components ← Array.range sz.nat?.get! |>.mapM (getElemVectorOfIdx arg)
              return acc.append components
         else
         if isStructure (←getEnv) name
         then let components ← componentsOf arg
              return acc.append components
         else return acc.push arg
    else return acc
  let zmodType ← inferType <| ←args'[0]?.getDM (throwError m!"No explicit arguments found.")
  let args' ← mkAppM ``Array.mk #[←mkListLit zmodType args'.toList]
  withLocalDecl `wg .default (.app (.const ``Wg []) (.const p [])) fun fvar ↦ do
    let body ← mkAppM ``Wg.run #[fvar, args']
    mkLambdaFVars (#[fvar] ++ argFvars) body

def compile (p circuitName : Name) (f : Expr) (n : Nat) : TermElabM Unit := do
  let serialiseS ← serialise p f
  trace[Clap.Compiler.serialise] m!"{serialiseS}"

  let curryS ← curry p serialiseS
  trace[Clap.Compiler.curry] m!"{curryS}"

  let reduceExprS ← reduceExpr n curryS
  trace[Clap.Compiler.reduce] m!"{reduceExprS}"

  let compiledF ← pure reduceExprS >>= toDeep p
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
  let wg ← wg p args
  let wgName := circuitName.appendAfter "_wg_wrap"
  addAndCompile <| .defnDecl {
    name        := wgName
    levelParams := []
    type        := ←inferType wg
    value       := wg
    hints       := .regular 18
    safety      := .safe
  }
  logInfo m!"Wg for {circuitName} is {wgName}."

def instantiateLambdaHeadInst (e : Expr) : TermElabM (Option Expr) := do
  let .lam _ type _ bi := e | return .none
  if bi.isInstImplicit
  then let withInstanceS ← instantiateLambda e #[←Elab.Term.mkInstMVar type]
       trace[Clap.Compiler.preprocess] m!"Resolved [{type}]:\n{withInstanceS}"
       return withInstanceS
  else return .none

partial def trySynthAll (e : Expr) : TermElabM Expr := do
  let .lam n t body bi := e | return e
  match ← instantiateLambdaHeadInst e with
  | .none => return .lam n t (←trySynthAll body) bi
  | .some e => trySynthAll e

def fixPrime (e p : Expr) : TermElabM Expr := do
  let withFixedPS ← instantiateLambda e #[p]
  trace[Clap.Compiler.preprocess] m!"{withFixedPS}"
  pure withFixedPS >>= trySynthAll >>= instantiateMVars

elab "#compile" circuit:ident "using" p:ident n:optional("iters" num) : command => Command.liftTermElabM do
  let defaultIters : ℕ := 2048
  /-
  This is just a debugging feature so I do not care to make it pretty.
  We sometimes get `.some <Nothing>` so we spoon to `defaultIters` one way or the other.
  -/
  let n := n.raw[1]?.elim defaultIters (let num := ·.toNat; if num == 0 then defaultIters else num)
  
  withTraceNode `Clap.Compiler (return m!"{exceptEmoji ·} Compiling {circuit} with {p} (iters = {n})") do
  let [decl] ← realizeGlobalConst circuit | throwError m!"Ambiguous constant: {circuit}"
  trace[Clap.Compiler.nameResolution] m!"Resolved {circuit} into {decl}"
  let .some decl := (←getEnv).find? decl | throwError m!"Undeclared constant: {circuit}"
  let preprocessedS ←
    withTraceNode `Clap.Compiler.preprocess
                  (Trace.formatExprWith s!"Fixed p = {p}, resolved typeclasses:") do
                  fixPrime decl.value! (.const p.getId [])
  compile p.getId circuit.getId preprocessedS n

end Compiler

end Clap
