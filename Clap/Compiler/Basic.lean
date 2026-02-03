import Lean
import Qq
import Mathlib.Tactic

import Clap.Simulation
import Clap.Spec
import Clap.Wheels

open Lean Qq

namespace Clap

variable {p : ℕ}

/--
Assumes `conclusion` has had its mvars instantiated.
-/
partial def lhsOfBisim (conclusion : Expr) : MetaM Expr := do
  let (``Clap.Simulation.sBisim, ⟨_ :: _ :: lhs :: _⟩) := conclusion.getAppFnArgs
    | throwError m!"{conclusion} is not `Simulation.sBisim.\nRaw expr: {repr conclusion}."
  return lhs

def putOnTopIdx (n : Nat) (goals : List MVarId) : List MVarId :=
  goals[n]! :: goals.eraseIdx n

def unassignedGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM (not <$> ·.isAssigned)

def putOnTop (what : Expr → Bool) (goals : List MVarId) : MetaM (List MVarId) := do
  if goals.isEmpty then return []
  let n := (←goals.mapM (·.getType')).findIdx what
  if n == goals.length then throwError m!"No bisimulation goal in:\n{goals}"
  return putOnTopIdx n goals

structure Goals where
  inference : Option MVarId
  rest : List MVarId
  deriving Repr

namespace Goals

def unassignedGoals (goals : Goals) : MetaM Goals :=
  Clap.unassignedGoals goals.rest <&> ({goals with rest := ·})

def toLeanGoals (goals : Goals) : List MVarId :=
  goals.inference.toList ++ goals.rest

def runTactic (goals : Goals) (lem : Syntax) : MetaM Goals := do
  let .some inferenceGoal := goals.inference | return goals
  let (inferenceGoals, _) ← inferenceGoal.withContext do
    Elab.runTactic inferenceGoal (←`(tactic|$(⟨lem⟩)))
  match inferenceGoals with
  | [] => return {goals with inference := .none}
  | inferenceGoals =>
    let newInference :: restInference ← putOnTop (·.isAppOf ``Clap.Simulation.sBisim) inferenceGoals
      | throwError m!"Logic error: `putOnTop should have thrown a 'no bisimulation error'"
    return ⟨newInference, goals.rest ++ restInference⟩

def seqTacs (goals : Goals) : List Syntax → MetaM (Option Goals)
  | [] => return .none
  | tac₁ :: rest => (.some <$> goals.runTactic tac₁) <|> seqTacs goals rest

def lineariseHeadBinds (goals : Goals) : MetaM Goals := do
  goals.runTactic (←`(tacticSeq| rw [bind_assoc]
                                 try (rw [Option.bind_eq_bind, Option.bind_some])))

def reduceMatch (goals : Goals) : MetaM Goals := do
  goals.runTactic (←`(tactic|dsimp -zeta +beta only))

partial def unfoldAny (goals : Goals) (e : Expr) : MetaM Goals := do
  let .some _ := goals.inference | return goals
  if let .const name _ := e.getAppFn then
    if ← Meta.isMatcher name
    then try let x ← goals.reduceMatch; return x catch _ =>
         let .some m ← Meta.getMatcherInfo? name | return goals
         let args := e.getAppArgs
         let mut goals := goals
         for discr in m.getDiscrRange.toArray do
           let t ← Meta.inferType args[discr]!
           if (←Meta.inferType t).isProp then continue
           goals ← unfoldAny goals args[discr]!
         return goals
    else if (←isIrreducible name) || (←Meta.isConstructorApp e)
         then return goals
         else let nameStx := mkIdent name
              goals.runTactic (←`(tactic|first | dsimp -zeta +beta only [$nameStx:ident] | unfold $nameStx))
              -- goals.runTactic (←`(tactic|first | dsimp -zeta +beta only [$nameStx:ident] | unfold $nameStx))
        /-
          Why not just unfold:
            `return {goals with inference := ←Meta.unfoldTarget inferenceGoal name}`

          The trick is to use `dsimp`'s smart unfolding and override some of the smartness
          with manually handling some cases, such as the matcher logic.
        -/
  else
    let .proj (struct := struct) .. := e.getAppFn | return goals
    let .const name _ := struct.getAppFn | return goals
    goals.runTactic (←`(tactic|dsimp -zeta +beta only [$(mkIdent name):ident]))

def bindPure (goals : Goals) : MetaM Goals := do
  -- goals.unfoldAny
  goals.runTactic (←`(tacticSeq| try rw [Option.pure_def]
                                 try rw [Option.bind_eq_bind]
                                 rw [Option.bind_some]))

end Goals

private lemma Spec.Compiler.ext_lam [Fact (Nat.Prime p)] {α : Type}
  {f : ZMod p → α} {g : ZMod p → Circuitₑ p} {g' : Circuitₑ p}
  (h : Simulation.sBisim f (Circuit.lam g).eval)
  (hint : g' = Circuit.lam g) :
  Simulation.sBisim f g'.eval := by grind

/--
TODO(cleanup) - We should not always be checking for the outermost bind. Pass in the 'next' thing.
-/
def isBindBind (lhs : Expr) : MetaM Bool := do
  let (`Bind.bind, ⟨_ :: _ :: _ :: _ :: f :: _⟩) := lhs.getAppFnArgs | return false
  return f.isAppOf ``Bind.bind || f.isAppOf ``Option.bind

/--
TODO(cleanup) - We should not always be checking for the outermost bind. Pass in the 'next' thing.
-/
def isBindPure (lhs : Expr) : MetaM Bool := do
  let (`Bind.bind, ⟨_ :: _ :: _ :: _ :: f :: _⟩) := lhs.getAppFnArgs | return false
  return f.isAppOf ``Pure.pure || f.isAppOf ``Option.some

/--
TODO(cleanup) - We should not always be checking for the outermost bind. Pass in the 'next' thing.
-/
def isForInVector (lhs : Expr) : MetaM Bool := do
  -- logInfo m!"LHS: {lhs}"
  let (``Bind.bind, ⟨_ :: _ :: _ :: _ :: f :: _⟩) := lhs.getAppFnArgs | return false
  let (``ForIn.forIn, ⟨_ :: t :: _⟩) := f.getAppFnArgs | return false
  return t.isAppOf `Vector

set_option hygiene false in -- We'll see about this one, tired of `mkIdent` :).
/--
Use `lhs` for granular control over matching if needed.
-/
def step (goals : Goals) : MetaM Goals := do
  -- TODO(workaround) I am not sure how safe this is.
  let goals ← goals.runTactic (←`(tactic|try extract_lets))
  let goals ← goals.runTactic (←`(tactic|repeat rw [←Option.bind_eq_bind]))

  let lhs ← lhsOfBisim (←goals.inference.get!.getType')

  -- TODO(cleanup) LineariseBinds overlaps bindPure
  if ←isBindBind lhs
  then goals.lineariseHeadBinds
  else
  if ←isBindPure lhs
  then goals.bindPure
  else
    let goals' ← goals.seqTacs <|
      -- TODO(workaround) We want to synthesise this list automatically.
      ([] : List (TSyntax `tactic)) ++
      -- TODO(simplicity) We want an attribute that attaches the lemmas.
      [
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.ext_lam)
                            (h := $(mkIdent `Simulation.sBisim.lam) fun _ ↦ ?_))),
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.equiv_accept))),
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.equiv_eq0)
                            (er := $(mkIdent `Exp.c) _)
                            (h := rfl))),
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.equiv_share)
                            (er := $(mkIdent `Exp.c) _)
                            (h := rfl)
                            (cont := fun _ ↦ ?_))),
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.equiv_is_zero)
                            (er := $(mkIdent `Exp.c) _)
                            (h := rfl)
                            (cont := fun _ ↦ ?_))),
        (←`(tactic|apply $(mkIdent ``Clap.Spec.Compiler.equiv_num2bits)
                            (er := $(mkIdent `Exp.c) _)
                            (h := rfl)
                            (cont := fun _ ↦ ?_))),
      ]
    goals'.getDM do
      let (`Bind.bind, ⟨_ :: _ :: _ :: _ :: f :: _⟩) := lhs.getAppFnArgs | return goals
      goals.unfoldAny f
  >>= Goals.unassignedGoals

def extractTac (inferenceGoal : MVarId) : MetaM Goals := do
  let mut goals ← (⟨·, []⟩) <$> tryCatch (reduceCurry inferenceGoal) fun _ ↦ pure inferenceGoal
  while true do
    match goals.inference with
    | .none => break
    | .some _ => goals ← step goals
  return goals

open Elab Tactic in
elab "extract" "using" name:ident : tactic => do
  evalTactic (←`(tacticSeq|unfold $name
                           constructor))
  let (proof :: rest) ← getUnsolvedGoals | throwError "Expected two goals; proof and witness."
  extractTac proof >>= setGoals ∘ (·.toLeanGoals ++ rest)
  evalTactic (←`(tactic|any_goals rfl))

private def explodeVec (name : Name) (len : Nat) : String :=
  String.intercalate " " <| List.range len |>.map fun i ↦ s!"{name}[{i}]"

private def explodeStruct (name : Name) (argmap: Std.HashMap Name (Array Name)) (type : Name) : String :=
  -- dbg_trace s!"name: {name} argmap: {repr argmap} type: {type} rtype: {argmap.contains type}"
  String.intercalate " " <| argmap[type]!.toList |>.map fun proj ↦ s!"{name}.{proj}"

open Meta Elab Term Command in
elab "#compile" circuit:ident : command => do
  let .some decl := (←getEnv).find? circuit.getId | throwError m!"Undeclared constant: {circuit}"
  let (preamble, implicits, vecs, argmap, customTypes) ← liftTermElabM <| forallTelescopeReducing decl.type fun args _ ↦ do
    let mut preamble := ""
    let mut implicits := ""
    let mut vecs := #[]
    -- Can technically use ProjectionFunctionInfo.i
    let mut argmap : Std.HashMap Name (Array Name) := {}
    let mut customTypes := #[]
    let mut depth := 1
    for arg in args do
      if (←arg.fvarId!.getDecl).binderInfo == .implicit
      then implicits := implicits ++ s!"\{{←PrettyPrinter.ppExpr arg}} "
           continue
      let t ← Meta.inferType arg
      let userName ← arg.getAppFn.fvarId!.getUserName
      if let (`Vector, #[_, len]) := t.getAppFnArgs then
        vecs := vecs.push (userName, len.nat?.get!, (←PrettyPrinter.ppExpr t).pretty, s!"{userName}")
        preamble := preamble ++ s!"Clap.curry fun ({userName} : {←PrettyPrinter.ppExpr t}) ↦ "
        depth := depth + 1
      else
        let typeName := t.getAppFn.constName
        if !isStructure (←getEnv) typeName then continue
        customTypes := customTypes.push typeName
        let fields := getStructureFields (←getEnv) typeName
        vecs := vecs.push (userName, fields.size, s!"{(←PrettyPrinter.ppExpr t).pretty}", s!"{typeName}")
        preamble := preamble ++ s!"Clap.curry fun ({userName} : Vector (ZMod p) {fields.size}) ↦ "
        argmap := argmap.insert typeName fields
        -- logInfo m!"arg: {arg} of type: {t} s: {fields}"
    -- logInfo m!"vecs: {vecs} argmap: {repr argmap} customTypes: {customTypes}"
    return (preamble, implicits, vecs, argmap, customTypes)
  let body ←
    if customTypes.isEmpty
    then liftTermElabM <| lambdaTelescope decl.value! fun _ body ↦ PrettyPrinter.delab body
    else liftTermElabM <| lambdaTelescope decl.value! fun args body ↦ do
      let argNames ← args.mapM (·.fvarId!.getUserName)
      -- logInfo m!"body: {body}"
      let stx ← PrettyPrinter.delab body
      let newStx ← stx.replaceM fun s ↦ do
        try
          if s.isIdent && !argNames.contains s.getId then return .none
          let e ← elabTerm s .none
          let (name, _) := e.getAppFnArgs
          let isProj ← isProjectionFn name
          let isRelevant := customTypes.contains name.getPrefix
          if isProj && isRelevant then
            let (type, proj) := (name.getPrefix, name.components.getLast!)
            let idx := argmap[type]!.idxOf proj
            let `($f.$proj) := s | return .none -- TODO(generalise) - Technically needs to be more general for `Point.x p`.
            -- logInfo m!"s: {s}\nt: {e}\nf: {name}\nidx: {idx}\nf[{f}]-proj[{proj}]"
            return .some (←`(($f)[$(Syntax.mkNatLit idx)]))
        catch _ => return .none
        return .none
      -- logInfo m!"newBody: {body}\n\nnew: {stx}\nreplaced: {newStx}"
      return newStx
  let body ← Format.pretty <$> (liftTermElabM <| Lean.PrettyPrinter.ppCategory `command body)
    -- Format.pretty <$> PrettyPrinter.ppExpr e
  let circuitName := circuit.getId.components.getLast!
  let curriedCircuitName := s!"{circuitName}_curried"
  let declaration := s!"open Clap.Spec in def {curriedCircuitName} {implicits}:= {preamble}{body}"
  let .ok declStx := Parser.runParserCategory (←getEnv) `command declaration
    | throwError m!"Failed to compile: {declaration}"
  logInfo m!"{declStx}"
  elabCommand declStx
  logInfo m!"Circuit: {curriedCircuitName}"
  let explodedVecs := vecs.foldl (init := "") fun acc (name, len, _, _) ↦ s!"{acc} {explodeVec name len}"
  let args := vecs.foldl (init := "") fun acc (name, _, type, _) ↦ acc ++ s!" \{{name} : {type}}"
  -- TODO(simpler) - There's a better solution here. More specifically, we don't need this equality.
  -- It would be fine to simply show equivalence with respect to bisimulation, which is easier.
  let equiv_proof :=
    s!"theorem {curriedCircuitName}_equiv{args} : {circuitName} " ++
    s!"{" ".intercalate (vecs.map (toString ∘ Prod.fst)).toList}" ++
    s!" = {curriedCircuitName}{explodedVecs} := by first | rfl | sorry"
  let .ok prfStx := Parser.runParserCategory (←getEnv) `command equiv_proof
    | throwError m!"Failed to compile: {equiv_proof}"
  -- Redundant with match.
  if customTypes.isEmpty then
    elabCommand prfStx
    logInfo m!"Proof: {curriedCircuitName}_equiv"
  match (←getEnv).find? (.mkStr2 "Clap" s!"{curriedCircuitName}_equiv") with
  | .none => let args := vecs.foldl (init := "") fun acc (name, _, t, _) ↦ acc ++ s!" \{{name} : {t}}"
             let explodedVecs := vecs.foldl (init := "") fun acc (name, len, type, typename) ↦
               s!"{acc} {explodeStruct name argmap (.mkStr2 (typename.splitOn ".")[0]! (typename.splitOn ".")[1]!)}"
             let equiv_proof :=
               s!"theorem {curriedCircuitName}_equiv{args} : {circuitName} " ++
               s!"{" ".intercalate (vecs.map (toString ∘ Prod.fst)).toList}" ++
               s!" = {curriedCircuitName}{explodedVecs} := by first | rfl | sorry"
             logInfo m!"equiv_proof: {equiv_proof}"
             let .ok prfStx := Parser.runParserCategory (←getEnv) `command equiv_proof
               | throwError m!"Failed to compile: {equiv_proof}"
             elabCommand prfStx
  | .some decl =>
    if decl.value!.hasSorry
    then logWarning <| s!"Cannot synthesise the proof of {curriedCircuitName}_equiv. Using sorry." ++
                      s!"\nNOTE: The solution here is to simply generate a proof of equivalence, " ++
                      s!"not equality. TODO(easy)."

section EXAMPLES

variable [Fact (Nat.Prime p)]

open Spec Compiler

def exAll (i: ZMod p) : Option Unit := do
  eq0 i
  let i <- share i
  let i <- is_zero i
  let _is <- num2bits 2 i
  accept

def extract_manual_all :
  { c:Circuitₑ p // Simulation.sBisim (exAll (p := p)) c.eval } := by
  extract using exAll

structure Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def ex₀ (point : Point p) : Option Unit := do
  eq0 (point.x + point.y)
  eq0 (point.x + point.z)
  accept

#compile Clap.ex₀

def extract_manual₀ :
  { c:Circuitₑ p // Simulation.sBisim (ex₀_curried (p := p)) c.eval } := by
  extract using ex₀_curried

example : (extract_manual₀ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.lam fun x_1 =>
      Circuit.lam fun x_2 =>
        Circuit.eq0 (Exp.c (x + x_1))
          (Circuit.eq0 (Exp.c (x + x_2)) Circuit.nil) := rfl


def ex₁ (i : ZMod p) : Option Unit := do
  accept

def extract_manual₁ :
  { c:Circuitₑ p // Simulation.sBisim (ex₁ (p := p)) c.eval } := by
  unfold ex₁
  refine ⟨?c,?p⟩
  case' p =>
    apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?rest)
  case rest =>
    apply equiv_accept
  rfl

def extract_automatic₁ :
  { c : Circuitₑ p // Simulation.sBisim (ex₁ (p := p)) c.eval } := by
  extract using ex₁

example : (extract_automatic₁ (p := p)).1 = Circuit.lam fun _ => Circuit.nil := rfl

def ex₂ (i: ZMod p) : Option Unit := do
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  accept

def extract_automatic₂ :
  { c : Circuitₑ p // Simulation.sBisim (ex₂ (p := p)) c.eval } := by
  extract using ex₂

example : (extract_automatic₂ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.eq0 (Exp.c x)
      (Circuit.eq0 (Exp.c x)
        (Circuit.eq0 (Exp.c x)
          (Circuit.eq0 (Exp.c x)
            (Circuit.eq0 (Exp.c x)
              (Circuit.eq0 (Exp.c x)
                (Circuit.eq0 (Exp.c x)
                  (Circuit.eq0 (Exp.c x)
                    (Circuit.eq0 (Exp.c x) Circuit.nil)))))))) := rfl

def ex₃ (i : ZMod p) : Option Unit := do
  eq0 i
  let vi ← share i
  eq0 (vi + i)
  accept

def extract_manual₃ :
  { c : Circuitₑ p // Simulation.sBisim (ex₃ (p := p)) c.eval } := by
  unfold ex₃
  refine ⟨?c,?p⟩
  swap
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_right 2
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_share (er := Exp.v _) (h := rfl) (cont := fun _ ↦ ?_)
  swap
  apply equiv_eq0 (er:=Exp.c _) (h := rfl)
  apply equiv_accept
  swap
  rfl

def extract_automatic₃ :
  { c : Circuitₑ p // Simulation.sBisim (ex₃ (p := p)) c.eval } := by
  extract using ex₃

example : (extract_automatic₃ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.eq0 (Exp.c x)
      (Circuit.share (Exp.c x)
        fun x_1 => Circuit.eq0 (Exp.c (x_1 + x)) Circuit.nil) := rfl

-- This is (eq0 i); baby steps.
def ex₄ (i : ZMod p) : Option Unit := do
  let x ← is_zero i
  eq0 (1 - x)
  accept

def extract_manual₄ :
  { c : Circuitₑ p // Simulation.sBisim (ex₄ (p := p)) c.eval } := by
  unfold ex₄
  refine ⟨?c,?p⟩
  swap
  apply ext_lam (h := Simulation.sBisim.lam fun X ↦ ?rest)
  rotate_right 2
  apply equiv_is_zero (er := Exp.c _) (h := rfl) (cont := fun _ ↦ ?_)
  swap
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_accept
  swap
  rfl

def extract_automatic₄ :
  { c : Circuitₑ p // Simulation.sBisim (ex₄ (p := p)) c.eval } := by
  extract using ex₄

example : (extract_automatic₄ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.is_zero (Exp.c x) fun x =>
      Circuit.eq0 (Exp.c (1 - x)) Circuit.nil := rfl

def ex₅ (is₁ : ZMod p) (is₂ : ZMod p) : Option Unit := do
  eq0 is₁
  let vi <- share is₁
  eq0 (vi + is₂)
  accept

def extract_automatic₅ :
  { c : Circuitₑ p // Simulation.sBisim (ex₅ (p := p)) c.eval } := by
  extract using ex₅

example : (extract_automatic₅ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.lam fun x_1 =>
      Circuit.eq0 (Exp.c x)
        (Circuit.share (Exp.c x) fun x => Circuit.eq0 (Exp.c (x + x_1)) Circuit.nil) := rfl

def ex₆ :=
  curry fun (is : Vector (ZMod p) 2) ↦ do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  return accept

def extract_automatic₆ :
  { c : Circuitₑ p // Simulation.sBisim (ex₆ (p := p)) c.eval } := by
  extract using ex₆

example : (extract_automatic₆ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.lam fun x_1 =>
      Circuit.eq0 (Exp.c x)
        (Circuit.share
          (Exp.c x) fun x_2 => Circuit.eq0 (Exp.c (x_2 + x_1)) Circuit.nil) := rfl

def ex₇ :=
  curry fun (xs: Vector (ZMod p) 2) ↦
  curry fun (ys: Vector (ZMod p) 2) ↦
  curry fun (zs: Vector (ZMod p) 2) ↦ do
  eq0 (xs[0] - zs[1])
  eq0 (xs[1] - zs[0])
  eq0 (ys[0] - zs[0])
  eq0 (ys[1] - xs[1])
  return accept

def extract_manual₇ :
  { c:Circuitₑ p // Simulation.sBisim (ex₇ (p := p)) c.eval } := by
  unfold ex₇
  refine ⟨?c,?p⟩
  swap
  dsimp -zeta only [curry]
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_right 2
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_right 5
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_right 8
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply ext_lam (h := Simulation.sBisim.lam fun _ ↦ ?_)
  rotate_left 3
  dsimp
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_eq0 (er := Exp.c _) (h := rfl)
  apply equiv_accept
  any_goals rfl

def extract_automatic₇ :
  { c : Circuitₑ p // Simulation.sBisim (ex₇ (p := p)) c.eval } := by
  extract using ex₇

example : (extract_automatic₇ (p := p)).1 =
  Circuit.lam fun x =>
    Circuit.lam fun x_1 =>
      Circuit.lam fun x_2 =>
        Circuit.lam fun x_3 =>
          Circuit.lam fun x_4 =>
            Circuit.lam fun x_5 =>
              Circuit.eq0 (Exp.c (x   - x_5))
             (Circuit.eq0 (Exp.c (x_1 - x_4))
             (Circuit.eq0 (Exp.c (x_2 - x_4))
             (Circuit.eq0 (Exp.c (x_3 - x_1)) Circuit.nil))) := rfl

def ex₈ (xs : Vector (ZMod p) 3) : Option Unit := do
  for x in xs do
    eq0 x

#compile Clap.ex₈

def extract_automatic₈ :
  { c : Circuitₑ p // Simulation.sBisim (ex₈_curried (p := p)) c.eval } := by
  extract using ex₈_curried

example : (extract_automatic₈ (p := p)).1 =
    Circuit.lam fun x =>
      Circuit.lam fun x_1 =>
        Circuit.lam fun x_2 =>
          Circuit.eq0 x
            (Circuit.eq0 x_1
              (Circuit.eq0 x_2
                Circuit.nil)) := rfl

#print ex₈_curried

#print extract_automatic₈._proof_4

end EXAMPLES

end Clap
