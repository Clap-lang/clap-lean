import Clap.Model.eDSL
import Clap.Model.Loop

/-!
# Source locations for ClapM programs

`clap def` elaborates a ClapM definition exactly as written and also as traced copy
`<name>.traced`. The copy runs the same program in `LocatedM`. Each bind is wrapped in
`Location.at` with its file, line, column and source text, so the run also records which source
line built which heap nodes and emitted which gates.
-/

namespace Clap

/-- A source position of a bind in a `clap def` body. -/
structure Site where
  decl : String
  file : String
  line : Nat
  col : Nat
  text : String
  deriving Repr, BEq, Hashable, Inhabited

/-- A call-stack node `site`, called from the stack `parent`. -/
structure StackNode where
  parent : Option Nat
  site : Nat
  deriving Repr, BEq, Hashable, Inhabited

/-- One run of a located bind -/
structure Entry where
  stack : Nat
  heapStart : Nat
  heapEnd : Nat
  gateStart : Nat
  gateEnd : Nat
  deriving Repr, Inhabited

structure Trace where
  sites : Array Site := #[]
  siteIds : Std.HashMap Site Nat := {}
  callStacks : Array StackNode := #[]
  callStackIds : Std.HashMap StackNode Nat := {}
  /-- in start order, so the innermost entry containing a ref is the last one that does -/
  entries : Array Entry := #[]
  /-- call stacks of the binds currently running, innermost first -/
  running : List Nat := []
  /-- gates emitted so far -/
  gates : Nat := 0

namespace Trace

def internSite (tr : Trace) (site : Site) : Nat × Trace :=
  match tr.siteIds[site]? with
  | some i => (i, tr)
  | none => (tr.sites.size, { tr with sites := tr.sites.push site, siteIds := tr.siteIds.insert site tr.sites.size })

def internStack (tr : Trace) (node : StackNode) : Nat × Trace :=
  match tr.callStackIds[node]? with
  | some i => (i, tr)
  | none => (tr.callStacks.size, { tr with callStacks := tr.callStacks.push node, callStackIds := tr.callStackIds.insert node tr.callStacks.size })

/-- The stack of the innermost bind that built heap node `ref`. Because of hash-consing, this is
where the node was first built. -/
def stackOfRef (tr : Trace) (ref : ExprRef) : Option Nat :=
  (tr.entries.findRev? fun e ↦ e.heapStart ≤ ref && ref < e.heapEnd).map (·.stack)

/-- The stack of the innermost bind that emitted gate `gate`. -/
def stackOfGate (tr : Trace) (gate : Nat) : Option Nat :=
  (tr.entries.findRev? fun e ↦ e.gateStart ≤ gate && gate < e.gateEnd).map (·.stack)

/-- The sites of a stack, innermost first. -/
def frames (tr : Trace) (stack : Nat) : List Site :=
  go tr.callStacks.size stack
where
  go : Nat → Nat → List Site
    | 0, _ => []
    | fuel + 1, i =>
      match tr.callStacks[i]? with
      | none => []
      | some node =>
        let rest := match node.parent with
          | some parent => go fuel parent
          | none => []
        match tr.sites[node.site]? with
        | some site => site :: rest
        | none => rest

end Trace

variable {p : ℕ}

/-- `ClapM` with a `Trace` on the side. A plain `def`, so that only the instances below apply. -/
def LocatedM (p : ℕ) (α : Type) : Type := StateT Trace (ClapM p) α

namespace LocatedM

instance : Monad (LocatedM p) := inferInstanceAs (Monad (StateT Trace (ClapM p)))

/-- Run `act` and also return how many gates it emitted. -/
def listenGates {α : Type} (act : ClapM p α) : ClapM p (α × Nat) :=
  WriterT.mk do
    let (a, gates) ← WriterT.run act
    pure ((a, gates.size), gates)

instance : MonadLift (ClapM p) (LocatedM p) where
  monadLift {α} (act : ClapM p α) : LocatedM p α := fun tr ↦ do
    let (a, gates) ← listenGates act
    pure (a, { tr with gates := tr.gates + gates })

def heapSize : ClapM p Nat := liftM (m := HashConsM p) (n := ClapM p) do return (← HashConsM.getExprs).size

/-- Run from `numAlloc` and `σ`, like `ClapM.run`, also returning the trace. -/
def run {α : Type} (prog : LocatedM p α) (numAlloc : ℕ) (σ : HashConsSt p) :
    (((α × Trace) × Circuit) × ℕ) × HashConsSt p :=
  ClapM.run (StateT.run (prog : StateT Trace (ClapM p) α) {}) numAlloc σ

/-- Step `i` of a `LocatedM` loop as a `ClapM` step on the loop state and the trace. -/
def loopStep {β : Type} (f : ℕ → β → LocatedM p (ForInStep β)) (i : ℕ) (state : β × Trace) :
    ClapM p (ForInStep (β × Trace)) := do
  let (step, tr) ← (f i state.1 : StateT Trace (ClapM p) (ForInStep β)) state.2
  pure <| match step with
    | .done b => .done (b, tr)
    | .yield b => .yield (b, tr)

/-- `for i in loopRange n do …` in a traced copy -/
instance : ForIn (LocatedM p) LoopRange ℕ where
  forIn r init f := fun tr ↦ forIn (m := ClapM p) r (init, tr) (loopStep f)

section Proofs

variable {α γ β : Type}

theorem bind_apply (x : LocatedM p α) (g : α → LocatedM p γ) (tr : Trace) :
    (x >>= g) tr = (x tr : ClapM p (α × Trace)) >>= fun (a, tr') ↦ g a tr' := rfl

theorem pure_apply (a : α) (tr : Trace) : (pure a : LocatedM p α) tr = pure (a, tr) := rfl

/-- A `LocatedM` list loop is the `ClapM` list loop of `loopStep`. -/
theorem forIn_list_apply (l : List ℕ) (b : β) (f : ℕ → β → LocatedM p (ForInStep β))
    (tr : Trace) :
    (forIn l b f : LocatedM p β) tr = forIn (m := ClapM p) l (b, tr) (loopStep f) := by
  induction l generalizing b tr with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.forIn_cons, bind_apply]
    simp only [loopStep, bind_assoc, pure_bind]
    congr 1
    funext x
    rcases x with ⟨s, tr'⟩
    cases s <;> simp [pure_apply, ih]

/-- `for i in loopRange stop start` in `LocatedM` runs the steps of the list loop. -/
theorem forIn_loopRange (r : LoopRange) (init : β) (f : ℕ → β → LocatedM p (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start (r.stop - r.start)) init f := by
  funext tr
  change forIn (m := ClapM p) r (init, tr) (loopStep f) = _
  rw [ClapM.forIn_loopRange, forIn_list_apply]

/-- `for i in loopRange stop start` in `LocatedM` is `for i in [start:stop]`. -/
theorem forIn_loopRange_eq_forIn_range (start stop : ℕ) (init : β)
    (f : ℕ → β → LocatedM p (ForInStep β)) :
    forIn (loopRange stop start) init f = forIn [start:stop] init f := by
  rw [forIn_loopRange, Std.Legacy.Range.forIn_eq_forIn_range']
  simp [loopRange, Std.Legacy.Range.size]

end Proofs

end LocatedM

/-- Run `act` as the bind at `site`. record the heap refs it builds and the gates it emits. -/
def Location.at {α : Type} (site : Site) (act : LocatedM p α) : LocatedM p α := fun tr ↦ do
  let heapStart ← LocatedM.heapSize
  let (siteId, tr) := tr.internSite site
  let (stack, tr) := tr.internStack ⟨tr.running.head?, siteId⟩
  let entry := tr.entries.size
  let tr := { tr with
    entries := tr.entries.push ⟨stack, heapStart, heapStart, tr.gates, tr.gates⟩
    running := stack :: tr.running }
  let (a, tr) ← (act : StateT Trace (ClapM p) α) tr
  let heapEnd ← LocatedM.heapSize
  pure (a, { tr with
    entries := tr.entries.modify entry fun e ↦ { e with heapEnd, gateEnd := tr.gates }
    running := tr.running.tail })

/-- `Location.at` for a plain `ClapM` action -/
def Location.atM {α : Type} (site : Site) (act : ClapM p α) : LocatedM p α :=
  Location.at site (monadLift act)

/-- The traced copy of a ClapM program. `clap def` adds an instance for each definition, any other
program falls back to running without locations. -/
class HasTrace {α : Type} (prog : ClapM p α) where
  traced : LocatedM p α

instance (priority := low) instHasTraceLift {α : Type} (prog : ClapM p α) : HasTrace prog :=
  ⟨monadLift prog⟩

/-! ## `clap def` -/

section Command

open Lean Elab Command Term Meta Parser.Term

/-- `clap def foo … := body` elaborates `foo` unchanged, then the traced copy `foo.traced`. -/
syntax (name := clapDef) "clap " Lean.Parser.Command.declaration : command

namespace ClapDef

/-- The source file of module `mod`, relative to the package root. Components are not escaped -/
def moduleFile (mod : Name) : String :=
  (System.mkFilePath (mod.components.map (·.toString (escape := false)))).toString ++ ".lean"

/-- The file of the current module, relative to the package root. -/
def currentFile : CommandElabM String := do
  let mod ← getMainModule
  if mod.isAnonymous then return (← getFileName)
  return moduleFile mod

/-- One line of source text, whitespace runs collapsed, at most 80 characters. -/
def collapse (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut space := false
  for c in s.toList do
    if c.isWhitespace then
      space := true
    else
      if space && !out.isEmpty then out := ' ' :: out
      space := false
      out := c :: out
  let text := out.reverse
  if text.length > 80 then String.ofList (text.take 79) ++ "…" else String.ofList text

/-- The `Site` literal for `stx`, falling back to `fallback` when `stx` has no position. -/
def siteOf (decl file : String) (fallback stx : Syntax) : CommandElabM Term := do
  let fileMap ← getFileMap
  let ref := if stx.getPos?.isSome then stx else fallback
  let some start := ref.getPos? | return ← `(Clap.Site.mk $(quote decl) $(quote file) 0 0 "")
  let stop := ref.getTailPos?.getD start
  let pos := fileMap.toPosition start
  let text := collapse (String.Pos.Raw.extract fileMap.source start stop)
  `(Clap.Site.mk $(quote decl) $(quote file) $(quote pos.line) $(quote pos.column) $(quote text))

/-- `t` calling `c.traced` instead of `c`, when the head of `t` is a `clap def` `c`. -/
def redirect? (t : Syntax) : CommandElabM (Option Syntax) := do
  let head := if t.getKind == ``Lean.Parser.Term.app then t[0] else t
  unless head.isIdent do return none
  let some c ← (try some <$> resolveGlobalConstNoOverload head catch _ => pure none) | return none
  unless (← getEnv).contains (c ++ `traced) do return none
  let head' := mkIdentFrom head (c ++ `traced)
  return some (if t.getKind == ``Lean.Parser.Term.app then t.setArg 0 head' else head')

/-- Rewrite a body: wrap each bind, bare action and `(← e)` in `Location.atM` (or `Location.at` for
a call to another `clap def`, which then extends the call stack). `fine` also rewrites `do` blocks
nested inside terms (lambdas); `site?` is the statement a `doExpr` belongs to. -/
partial def rewrite (decl file : String) (fallback : Syntax) (fine : Bool) (stx : Syntax)
    (site? : Option Syntax := none) : CommandElabM Syntax := do
  let go (s : Syntax) (site? : Option Syntax := none) := rewrite decl file fallback fine s site?
  match stx with
  | .node info kind args =>
    if kind == ``Lean.Parser.Term.doLetArrow || kind == ``Lean.Parser.Term.doReassignArrow then
      return .node info kind (← args.mapM (go · (some stx)))
    else if kind == ``Lean.Parser.Term.doIdDecl || kind == ``Lean.Parser.Term.doPatDecl then
      -- the right-hand side (argument 3) belongs to the enclosing `let`
      return .node info kind (← args.mapIdxM fun i a ↦ if i == 3 then go a site? else go a)
    else if kind == ``Lean.Parser.Term.doExpr then
      let t ← go args[0]!
      let site ← siteOf decl file fallback (site?.getD stx)
      let wrapped ← match ← redirect? t with
        | some traced => `(Clap.Location.at $site ($(⟨traced⟩)))
        | none => `(Clap.Location.atM $site ($(⟨t⟩)))
      return .node info kind (args.set! 0 wrapped)
    else if kind == ``Lean.Parser.Term.do && !fine then
      return stx
    else
      return .node info kind (← args.mapM (go ·))
  | _ => return stx

/-- Replace `ClapM` by `LocatedM` in a signature. -/
def locateSig (sig : Syntax) : Syntax :=
  Id.run <| sig.replaceM fun s ↦ pure <|
    match s.getId.eraseMacroScopes with
    | .str _ "ClapM" => if s.isIdent then some (mkIdentFrom s ``Clap.LocatedM) else none
    | _ => none

def tryElab (cmd : Syntax) : CommandElabM (Option Message) := do
  let saved ← get
  modify fun s ↦ { s with messages := {} }
  elabCommand cmd
  match (← get).messages.toList.find? (·.severity == .error) with
  | none =>
    modify fun s ↦ { s with messages := saved.messages, infoState := saved.infoState }
    return none
  | some error =>
    set saved
    return some error

/-- `instance : HasTrace (name xs…) := ⟨name.traced xs…⟩`. -/
def addHasTrace (name : Name) : CommandElabM Unit := liftTermElabM do
  let info ← getConstInfo name
  let us := info.levelParams.map mkLevelParam
  let (type, value) ← forallTelescope info.type fun xs _ ↦ do
    let prog := mkAppN (mkConst name us) xs
    let traced := mkAppN (mkConst (name ++ `traced) us) xs
    let cls ← mkAppM ``HasTrace #[prog]
    let inst ← mkAppOptM ``HasTrace.mk #[none, none, some prog, some traced]
    return (← mkForallFVars xs cls, ← mkLambdaFVars xs inst)
  let instName := name ++ `instHasTrace
  addAndCompile <| .defnDecl {
    name := instName, levelParams := info.levelParams, type, value
    hints := .abbrev, safety := .safe }
  setReducibleAttribute instName
  addInstance instName .global (eval_prio default)

end ClapDef

open ClapDef in
@[command_elab clapDef] def elabClapDef : CommandElab := fun stx ↦ do
  let decl := stx[1]
  elabCommand decl
  let `(Lean.Parser.Command.declaration| $mods:declModifiers def $id:declId $sig:optDeclSig := $body:term) := decl
    | logWarningAt stx[0] "clap: only `def … := …` gets a traced copy; errors will not show its source lines"
  let isPrivate := (mods.raw.find? (·.isOfKind ``Lean.Parser.Command.private)).isSome
  let mods' ← if isPrivate then `(declModifiers| private) else `(declModifiers|)
  let name := id.raw[0].getId
  let id' := mkIdentFrom id.raw[0] (name ++ `traced)
  let sig' : TSyntax ``Lean.Parser.Command.optDeclSig := ⟨locateSig sig⟩
  let decl := name.toString
  let file ← currentFile
  let rewriteBody (fine : Bool) : CommandElabM Term := do
    match body.raw with
    | .node info kind args => return ⟨.node info kind (← args.mapM (rewrite decl file body fine ·))⟩
    | other => return ⟨other⟩
  let whole ← `(Clap.Location.atM $(← siteOf decl file body body) ($body))
  let bodies ← if body.raw.getKind == ``Lean.Parser.Term.do then
      pure [← rewriteBody true, ← rewriteBody false, whole]
    else pure [whole]
  let mut firstError : Option Message := none
  let mut ok := false
  for body' in bodies do
    match ← tryElab (← `(command| $mods':declModifiers def $id':ident $sig' := $body')) with
    | none => ok := true; break
    | some error => firstError := firstError <|> some error
  unless ok do
    let reason ← match firstError with
      | some error => pure m!"\n{error.data}"
      | none => pure m!""
    logWarningAt stx[0] m!"clap: could not build the traced copy; errors will not show its source lines{reason}"
    return
  let some full := (← getEnv).find? (← resolveGlobalConstNoOverload id.raw[0]) |>.map (·.name)
    | return
  try addHasTrace full
  catch e => logWarningAt stx[0] m!"clap: no HasTrace instance: {e.toMessageData}"

end Command

end Clap
