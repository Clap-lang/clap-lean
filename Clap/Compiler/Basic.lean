import Mathlib.Data.ZMod.Basic

import Lean
import Qq

import Clap.Compilation
import Clap.Compiler.Deep
import Clap.Compiler.AddLets
import Clap.Lang
import Clap.Compiler.Reduce
import Clap.Compiler.Subexpression    

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

def curriedUserNamesAndElemTypeOfFVar (e : Expr) : MetaM (Option (Array Name × Expr)) := do
  let (``Vector, #[t, sz]) := (← inferType e).getAppFnArgs | return .none
  match sz.nat? with
  | .none => throwError "Cannot curry a Vector of an arbitrary size."
  | .some sz => return (curriedUserNamesOfSize (←e.fvarId!.getUserName) sz, t)

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
  let .some (names, _) ← curriedUserNamesAndElemTypeOfFVar arg | return .none
  let type ← mkAppM ``ZMod #[.const prime []]
  return .some (names.zip (Array.replicate names.size type))

def curriedBody (body : Expr) : TermElabM Expr := do
  let lctx ← getLCtx
  let res ← Meta.transform (skipConstInApp := true) body
    -- Replace every `x` with `#[x_0, ...]`.
    (pre := fun e ↦ do
      if e.isFVar
      then
        let .some (names, t) ← curriedUserNamesAndElemTypeOfFVar e | return .continue
        let array ← mkAppM ``Array.mk #[
          ←mkListLit t (←names.mapM (return lctx.findFromUserName? · |>.get!.toExpr)).toList
        ]
        let vecSansProof := mkAppN (.const ``Vector.mk [.zero]) #[t, toExpr names.size, array]
        let Expr.forallE _ t _ _ ← inferType vecSansProof | throwError "Expected function type."
        let vec := Expr.app vecSansProof (←mkEqRefl t)
        return .done vec
      else return .continue)
    -- And reduce `#[x₀, x₁, ..., xₖ][i (< k)]` to `xᵢ`.
    (post := fun e ↦ do
      if e.isAppOf ``GetElem.getElem
      then return .done (←Meta.reduce e) -- TODO: Do we need to be more specific than reduce?
      else return .continue)
  return res

def curry (prime : Name) (f : Expr) : TermElabM Expr := do
  lambdaTelescope f fun args body ↦ do
    withTransformedArgs args (liftM ∘ curryArg prime) fun _ ↦ do
      let res ← curriedBody body
      mkLambdaFVars
        (←(←getLCtx).getFVars.filterM fun fvar ↦ do return !(←inferType fvar).isAppOf ``Vector)
        res

def componentsOf (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let type ← inferType e
  let typeName := type.getAppFn.constName
  if !isStructure env typeName then throwError m!"{type} is not a structure."
  getStructureFields env typeName |>.mapM (mkProjection e)

def wg (p : Name) (argFvars : Array Expr) : TermElabM Expr := do
  let args' ← argFvars.foldlM (init := #[]) fun acc arg ↦ do
    let t ← inferType arg
    let .some name := t.getAppFn.constName? | return acc
    -- TODO: This handling is temporary. We'll be splitting on public/private inputs at some point.
    if (←arg.fvarId!.getBinderInfo).isExplicit
    then if ←isDefEq t.getAppFn (.const ``Vector [.zero])
         then let (``Vector, #[_, sz]) := t.getAppFnArgs | return acc
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

/--
TODO: Currently, we only do this processing at the very beginning.
Naturally, one actually has to do this after unfolds and all that.

TODO: With simp, this is likely superfluous, but let's keep it around for a bit.
-/
def sansInterfaceVectors (e : Expr) : TermElabM Expr := do
  Meta.transform e fun e ↦ do
    let_expr Vector.toList _ _ vec := e   | return .continue
    let_expr Vector.mk _ _ arr _   := vec | return .continue
    let_expr Array.mk _ l          := arr | return .continue
    trace[Clap.Compiler.sansInterfaceVectors] m!"{e}\n→\n{l}"
    return .done l

private def iterationsMessage (iters maxIters : ℕ) : MessageData :=
  m!"Reduction iterations[{iters}/{maxIters}]"

private def constantsSans (e : Expr) («instances» types : Bool := true) : MetaM (Array Name) := do
  let env ← getEnv
  e.getUsedConstants.filterM fun name ↦ do
    let .some ci := env.find? name | throwError "Unknown constant: {name}"
    let isPermitted (ci : ConstantInfo) : MetaM Bool :=
      let neutral := fun _ ↦ return true
      let null (f : ConstantInfo → MetaM Bool) (b : Bool) := if b then f else neutral
      let f := #[null notIsInstance «instances», null notIsType types].foldl (init := neutral)
                 fun f g ci ↦ return (←f ci) && (←g ci)
      f ci
    isPermitted ci
  where
    isFormerOf (ci : ConstantInfo) (f : Expr → Environment → Bool) : MetaM Bool := do
      forallTelescopeReducing ci.type fun _ conclusion ↦ return f conclusion (←getEnv)

    notIsInstance (ci : ConstantInfo) : MetaM Bool :=
      isFormerOf ci fun e env ↦ e.getAppFn.const?.elim true fun (name, _) ↦ !isClass env name

    notIsType (ci : ConstantInfo) : MetaM Bool :=
      isFormerOf ci fun e _ ↦ !e.isType
/--
We return the number of iterations the compiler took for reporting purposes.
-/
def compile (p circuitName : Name) (f : Expr) (maxIters : ℕ) (σ : CompileMap) : TermElabM ℕ := do
  let serialiseS ← serialise p f
  trace[Clap.Compiler.serialise] m!"{serialiseS}"

  let curryS ← withTraceNode `Clap.Compiler.curry
    Trace.formatExprWith do curry p serialiseS

  let sansInterfaceVectorsS ← withTraceNode `Clap.Compiler.sansInterfaceVectors
    Trace.formatExprWith do sansInterfaceVectors curryS

  let (reduceExprS, iters) ← withTraceNode `Clap.Compiler.reduce
    (fun e ↦
      match e with
      | .error _ => return crossEmoji
      | .ok (e, iters) => return m!"{checkEmoji}{iterationsMessage iters maxIters}:\n{e}"
    ) do reduceExpr maxIters sansInterfaceVectorsS σ

  -- IO.println s!"AST: {reduceExprS.sizeWithoutSharing}\nAST(shared): {←reduceExprS.numObjs}"
  -- IO.println s!"result:\n{reduceExprS}"
  trace[Clap.Compiler.usedConstants]
    m!"Constants (filtered):\n{←constantsSans reduceExprS}"

  try
    logInfo m!"DONE reduction"
    -- let withLets ← addLets reduceExprS
    -- logInfo m!"DONE withLets"
    let compiledF ← toDeep p reduceExprS
    logInfo m!"DONE toDeep"
    -- let compiledF := withLets

    let compiledFname := serialisedUserName circuitName
    addAndCompile <| .defnDecl {
      name        := compiledFname
      levelParams := []
      type        := ←inferType compiledF
      value       := compiledF
      hints       := .regular 18
      safety      := .safe
    }

    let sanitisedName (name : Name) : TermElabM Name := do
      let redundantPrefix := `Clap.Test.Compiler
      let [«prefix», suffix] := name.components.drop redundantPrefix.getNumParts |
        throwError "Malformed name."
      return Name.mkStr2 «prefix».toString suffix.toString

    logInfo m!"Compiled {circuitName} into {compiledFname}."
    let wgName := circuitName.appendAfter "_wg_wrap" -- TODO: Suspended WG.
    lambdaTelescope f fun args _ ↦ do
    let wg ← wg p args
    addAndCompile <| .defnDecl {
      name        := wgName
      levelParams := []
      type        := ←inferType wg
      value       := wg
      hints       := .regular 18
      safety      := .safe
    }
    logInfo m!"Wg for {circuitName} is {wgName}."

  catch exc =>
    throw <| Exception.error exc.getRef m!"{iterationsMessage iters maxIters}\n{exc.toMessageData}"

  return iters

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
  /-
  TODO: Workaround. As we started fixing `p`, this would break some assumptions.
  Needs a more robust approach.
  -/
  lambdaTelescope e fun args _ ↦ do
    let .some arg := args[0]? | throwError "No arguments in:\n{e}\n(TODO: Maybe this should work.)"
    let t ← inferType arg
    if !t.isConstOf ``Nat
    then trace[Clap.Compiler.preprocess] m!"Assuming fully applied function."
         return e
    let withFixedPS ← instantiateLambda e #[p]
    trace[Clap.Compiler.preprocess] m!"{withFixedPS}"
    pure withFixedPS >>= trySynthAll >>= instantiateMVars

def validateOptions : TermElabM Unit := do
  let options ← getOptions
  validateDebugTraceDebug options

where validateDebugTraceDebug (opt : Options) : TermElabM Unit := do
  let isDbg := opt.getBool `Clap.Compiler.Debug
  if isDbg then return
  let «prefix» := `trace.Clap.Compiler.Debug
  let dbgTraceOptions := «prefix».append <$> [`expressionSizeDelta, `revertOnTimeout]
  for option in dbgTraceOptions do
    if opt.getBool option then
      logWarning m!"{option} has no effect when Clap.Compiler.Debug = false"

def compileMeta (declName p : Name) (n : ℕ) (σ : CompileMap) : TermElabM Unit := do
  validateOptions
  discard <| withTraceNode `Clap.Compiler (fun e ↦
    match e with
    | .error err => return m!"{crossEmoji} Internal exception:\n{err.toMessageData}"
    | .ok iters => return m!"{checkEmoji} Compiling {declName} with {p} {iterationsMessage iters n}") do
    trace[Clap.Compiler.nameResolution] m!"Resolved {declName}"
    let .some decl := (←getEnv).find? declName | throwError m!"Undeclared constant: {declName}"
    let preprocessedS ←
      withTraceNode `Clap.Compiler.preprocess
                    Trace.formatExprWith do
                    fixPrime decl.value! (.const p [])
    compile p declName preprocessedS n σ

elab "#compile" circuit:ident "using" p:ident n:optional("iters" num) : command => Command.liftTermElabM do
  let [decl] ← realizeGlobalConst circuit | throwError m!"Ambiguous constant: {circuit}"
  let defaultIters : ℕ := 2048
  /-
  This is just a debugging feature so I do not care to make it pretty.
  We sometimes get `.some <Nothing>` so we spoon to `defaultIters` one way or the other.
  -/
  let n := n.raw[1]?.elim defaultIters (let num := ·.toNat; if num == 0 then defaultIters else num)
  compileMeta decl p.getId n {}

end Compiler

end Clap
