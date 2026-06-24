import Lean

namespace Clap.Compiler

open Lean

section DbgState

abbrev RuleHisto := Std.HashMap String (Nat × Float)

structure CompilerDbgState where
  ruleHisto : RuleHisto
  skippedRuleHisto : RuleHisto
  runUnfold: Bool
  deriving Inhabited

def sumRuleTime (times: RuleHisto) : Float :=
  (times.toArray.map (fun (_, (_, time)) ↦ time)).sum

initialize CompilerDbg : EnvExtension CompilerDbgState ←
  registerEnvExtension (pure default)

def getDbgState : MetaM CompilerDbgState :=
  return CompilerDbg.getState (←getEnv)

def CompilerDbgState.setRunUnfold (state: CompilerDbgState) (value: Bool) : CompilerDbgState := {
  state with runUnfold := value
}

def modifyDbgState (f : CompilerDbgState → CompilerDbgState) : MetaM Unit :=
  modifyEnv (CompilerDbg.modifyState (f := f))

def resetDbgState : MetaM Unit :=
  modifyDbgState (fun _ ↦ (default: CompilerDbgState).setRunUnfold false)

def getAndResetDbgState : MetaM CompilerDbgState := do
  let σ ← getDbgState
  resetDbgState
  return σ

def recordRuleDbg (e : String) (timeS : Float := 0.0) :=
  modifyDbgState fun σ ↦
    {σ with ruleHisto :=
      if σ.ruleHisto.contains e
      then σ.ruleHisto.modify e (fun (n, time) ↦ (Nat.succ n, time + timeS))
      else σ.ruleHisto.insert e (1, timeS)}

def recordSkippedRuleDbg (e : String) (timeS : Float := 0.0) :=
  modifyDbgState fun σ ↦
    {σ with skippedRuleHisto :=
      if σ.skippedRuleHisto.contains e
      then σ.skippedRuleHisto.modify e (fun (n, time) ↦ (Nat.succ n, time + timeS))
      else σ.skippedRuleHisto.insert e (1, timeS)}

open Std in
def _root_.Std.HashMap.modifyOrInsert!.{u, v} {α : Type u} {β : Type v}
                                              [BEq α] [Hashable α] [Inhabited β]
  (m : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  if m.contains a then m.modify a f else m.insert a default

inductive Pass where | structural | functional | general
  deriving Repr, Inhabited, DecidableEq, Hashable

instance : ToString Pass where
  toString pass :=
    match pass with
    | .structural => "structural"
    | .functional => "functional"
    | .general => "general"

open Pass

/--
TODO: Synth this to avoid mishaps.
  - e.g. look at syntax of `functional` in `Traverse.lean`
  - e.g. annotate with attributes
-/
def ruleMap : Std.HashMap String Pass :=
  .ofArray #[
    ("pureBindMany", structural),
    ("flattenBindsAny", structural),
    ("foldlM", structural)
  ] ∪
  .ofArray #[
    ("betaReduce", functional),
    ("zetaReduce", functional)
  ] ∪
  .ofArray #[
    ("getElem", general),
    ("append", general),
    ("range", general),
    ("evalGround", general),

    ("Vector.foldr_mk", general),
    ("foldr_toArray", general),
    ("List.foldr_cons", general),
    ("List.foldr_nil", general),

    ("Vector.sum_eq_foldr", general),

    ("Vector.size_toArray.size_toArray", general),
    ("List.size_toArray", general),
    ("List.length_cons", general),
    ("List.length_nil", general),
    ("set", general)
  ]

def passTimeOfHisto (histo : RuleHisto) : Std.HashMap Pass Float := Id.run do
  let mut result : Std.HashMap Pass Float := .ofArray #[
    (structural, 0.0),
    (functional, 0.0),
    (general, 0.0)
  ]
  for (rule, (_, time)) in histo do
    result := result.modify (ruleMap.get? rule |>.getD general) (· + time)
  return result

def CompilerDbgState.pretty (σ : CompilerDbgState) : MetaM Format := do
  let histoRules := σ.ruleHisto.toArray.qsort fun (_, _, timeₗ) (_, _, timeᵣ) ↦ timeₗ >= timeᵣ
  let histoSkippedRules := σ.skippedRuleHisto.toArray.qsort fun (_, _, timeₗ) (_, _, timeᵣ) ↦ timeₗ >= timeᵣ

  let text := String.intercalate "\n" ([
    f!"histoRules := {histoRules}",
    f!"totalStepTime := {sumRuleTime σ.ruleHisto}",
    f!"histoSkippedRules := {histoSkippedRules}",
    f!"totalSkipTime := {sumRuleTime σ.skippedRuleHisto}",
    f!"passTime := {repr <| passTimeOfHisto σ.ruleHisto}"
  ].map Format.pretty)
  return f!"{text}"

end DbgState

section Trace

abbrev ExprChanged? := Expr × Bool

abbrev ExprIter := Expr × Nat

def repeatEmoji := "🔁"

/-
TODO: Generalise these functions together with `formatExpr`
-/

def formatExprChanged?With {m : Type _ → Type _} [Monad m]
                           (s : String := "") (res : Except Exception ExprChanged?) : m MessageData :=
  return m!"{s}\n{
    match res with
    | .error _ => ""
    | .ok (res, isChanged) =>
      if isChanged then res else repeatEmoji
  }"

def formatExprIter {m : Type _ → Type _} [Monad m]
                   (s : String := "") (res : Except Exception ExprIter) : m MessageData :=
  return m!"{s}\n{
    match res with
    | .error _ => ""
    | .ok (res, iter) =>
      m!"Fixpoint reached after {iter} iteration(s).\n{res}"
  }"

end Trace

end Clap.Compiler
