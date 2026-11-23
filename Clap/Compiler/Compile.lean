import Clap.Compiler.toR1CS
import Clap.Compiler.Location
import Clap.Model.WitnessGenerator.toWg

open Clap.Serialize

/-!
# Compiling Clap programs

`Clap.compile prog numPublic numPrivate` lowers a ClapM program with `Circuit.toCs` and reduces
it with `toR1CS` (Clap/Compiler/toR1CS.lean). `Clap.compileWithWitness` also computes the witness
for given inputs and checks it against every row; `Clap.writeR1CS` writes the `.r1cs`, `.wtns`
and `.sym` files that snarkjs reads. On failure each returns a readable message. For a program
written with `clap def` (Clap/Compiler/Location.lean), each share site shows the source lines that
built the offending node, the value to share, and the gate; otherwise the message names the
assertion and the gate.

The pieces of that message are here too: expression rendering, the gate behind each assertion,
and the number of witness slots of a circuit.

Reading a report: `Circuit.toCs` keeps the expression heap indices and only appends nodes, so a
reported `e{ref}` below the ClapM heap size is the same `ExprRef` the gadget holds. `v{i}` is
trace slot `i` after `toCs` offsets (R1CS wire `i + 1`).
-/

namespace Clap.ConstraintSystem

variable {p : Nat} [Fact (Nat.Prime p)]

/-! ## Error messages -/

/-- Infix rendering of heap node `ref` with its precedence (3 for atoms, 2 for `*`, 1 for `+`,
`-` and negative constants). Binary nodes deeper than `depth`, or past the remaining node budget
in the state, print as `e{ref}`. A right operand of equal precedence keeps its parentheses, so
the printed shape is the heap shape. -/
def renderAux (σ : HashConsSt p) (depth : Nat) (ref : ExprRef) : StateM Nat (String × Nat) := do
  match σ[ref]? with
  | none => return (s!"e{ref}?", 3)
  | some (.c k) => return if 2 * k.val > p then (s!"-{p - k.val}", 1) else (toString k.val, 3)
  | some (.v i) => return (s!"v{i}", 3)
  | some (.binary_op l r op) =>
    match depth with
    | 0 => return (s!"e{ref}", 3)
    | depth + 1 =>
      let budget ← get
      if budget == 0 then return (s!"e{ref}", 3)
      set (budget - 1)
      let (sym, prec) := match op with
        | .add => ("+", 1)
        | .sub => ("-", 1)
        | .mul => ("*", 2)
      let (ls, lp) ← renderAux σ depth l
      let (rs, rp) ← renderAux σ depth r
      let ls := if lp < prec then s!"({ls})" else ls
      let rs := if rp ≤ prec then s!"({rs})" else rs
      return (s!"{ls} {sym} {rs}", prec)

/-- `ref` as an infix expression over variables `v{i}`, showing at most `nodes` binary nodes,
at most `depth` levels deep; the rest print as `e{ref}`. -/
def renderExpr (σ : HashConsSt p) (ref : ExprRef) (depth : Nat := 6) (nodes : Nat := 16) : String :=
  (Id.run ((renderAux σ depth ref).run' nodes)).1

/-- Number of assertions `Circuit.toCs` pushes for `gate` (the gadgets' `num_constraints_eq`). -/
def gateAssertions : Gate → Nat
  | .eq0 _ => eq0.num_constraints
  | .share _ => share.num_constraints
  | .isZero _ => isZero.num_constraints
  | .num2bits w _ => num2bits.num_constraints w
  | .fpmul w k .. => fpMul.num_constraints w k

def gateName : Gate → String
  | .eq0 _ => "eq0"
  | .share _ => "share"
  | .isZero _ => "isZero"
  | .num2bits w _ => s!"num2bits {w}"
  | .fpmul w k .. => s!"fpmul {w} {k}"

/-- For each assertion of `circuit.toCs`, the index of the gate that pushed it. -/
def _root_.Clap.Circuit.assertionGates (circuit : Circuit) : Array Nat :=
  circuit.zipIdx.flatMap fun (gate, g) ↦ Array.replicate (gateAssertions gate) g

/-- Number of witness slots of `circuit.toCs σ numInputs`: the inputs, then every gate's
`gateSlots` (Clap/Model/ConstraintSystem/toCs.lean). -/
def _root_.Clap.Circuit.numVars (circuit : Circuit) (numInputs : Nat) : Nat :=
  numInputs + (circuit.map gateSlots).sum

def ShareSite.render (σ : HashConsSt p) (origin : String) (site : ShareSite) : String :=
  let shown (ref : ExprRef) := s!"e{ref} := {renderExpr σ ref}"
  let (what, alternative) := match site.op with
    | .mul => (if site.operands.size > 1 then "product of two quadratic factors"
        else "product with a quadratic factor", "and  ")
    | .add => ("sum of two quadratics", "or   ")
    | .sub => ("difference of two quadratics", "or   ")
  let actions := site.operands.mapIdx fun i ref ↦
    s!"  {if i == 0 then "share" else alternative} {shown ref}"
  "\n".intercalate (#[s!"• {origin}: {what}", s!"    {shown site.node}"] ++ actions).toList

/-! ### Sites located in source, from a `clap def` trace -/

def siteLoc (s : Site) : String := s!"{s.file}:{s.line}:{s.col}"

/-- A call stack as a source frame: the innermost site as `┌─ file:line:col in decl` over its
line, then a `= called from …` note per caller. Also returns the padding that aligns more notes. -/
def frameLines (frames : List Site) : Option (String × Array String) := do
  let here ← frames.head?
  let pad := "".pushn ' ' ((toString here.line).length + 1)
  let mut lines := #[s!"{pad}┌─ {siteLoc here} in {here.decl}", s!"{here.line} │ {here.text}"]
  for outer in frames.tail do
    lines := lines.push s!"{pad}= called from {siteLoc outer} in {outer.decl}: {outer.text}"
  return (pad, lines)

/-- Where a share site comes from, as call stacks of the trace. -/
structure Located where
  /-- the bind that built the offending node; for a node built by `toCs`, its gate's bind -/
  built : Nat
  /-- the node was built by the gate's own constraints (`toCs`), not by the program -/
  inGate : Bool
  /-- the bind that emitted the gate behind the assertion, if any -/
  gate : Option Nat
  /-- the bind that built each operand, if any -/
  operands : Array (Option Nat)
  deriving BEq

/-- One site in a source-code frame, rustc/Noir style:
```
• product with a quadratic factor: e4 := v0 * v1 * v2
   ┌─ Clap/Test/R1CS/Pipeline.lean:60:2 in cubicProgram
60 │ let xyz ← xy * z
   = called from …
   = gate 0 (eq0) emitted at …: eq0 (← xyz - three)
   = share e3 := v0 * v1, built at …: let xy ← x * y
```
-/
def ShareSite.renderLocated (σ : HashConsSt p) (trace : Trace) (gate? : Option (Nat × Gate))
    (located : Located) (count : Nat) (site : ShareSite) : String := Id.run do
  let shown (ref : ExprRef) := s!"e{ref} := {renderExpr σ ref}"
  let what := match site.op with
    | .mul => if site.operands.size > 1 then "product of two quadratic factors"
        else "product with a quadratic factor"
    | .add => "sum of two quadratics"
    | .sub => "difference of two quadratics"
  let times := if count > 1 then s!" ({count} times)" else ""
  let some (pad, frame) := frameLines (trace.frames located.built) | return ""
  let mut lines := #[s!"• {what}{times}: {shown site.node}"] ++ frame
  if let some (g, gate) := gate? then
    if located.inGate then
      lines := lines.push s!"{pad}= the node is part of gate {g} ({gateName gate}), which this line emits"
    else
      match located.gate.bind (trace.frames · |>.head?) with
      | some s =>
        if located.gate != some located.built then
          lines := lines.push s!"{pad}= gate {g} ({gateName gate}) emitted at {siteLoc s}: {s.text}"
      | none => pure ()
  let alternative := if site.op == .mul then "and  " else "or   "
  for h : i in [0:site.operands.size] do
    let ref := site.operands[i]
    let built := match (located.operands[i]?).join.bind (trace.frames · |>.head?) with
      | some s => s!", built at {siteLoc s}: {s.text}"
      | none => ""
    lines := lines.push s!"{pad}= {if i == 0 then "share" else alternative} {shown ref}{built}"
  return "\n".intercalate lines.toList

/-- A readable message for `err`. `σ` is the heap the error refers to (`cs.σ`). With the circuit
that produced the system, each assertion also names its gate. With the trace of a `clap def`
program, each site shows the source lines that built it, and sites with the same source (a loop)
are shown once. -/
def CompileError.render (σ : HashConsSt p) (circuit : Option Circuit := none)
    (trace : Option Trace := none) : CompileError → String
  | .invalidRoot ref => s!"assertion root e{ref} is not in the expression heap"
  | .invalidVariable i => s!"variable v{i} is not one of the declared witness slots"
  | .invalidInputCount => "more inputs than witness slots"
  | .sizeOverflow => "the R1CS does not fit the header's 32/64-bit fields"
  | .witnessLength => "the trace length differs from the number of witness slots"
  | .needsShare sites => Id.run do
    let owners := (circuit.map Circuit.assertionGates).getD #[]
    let gateOf (a : Nat) : Option (Nat × Gate) := do
      let g ← owners[a]?
      return (g, ← circuit.bind (·[g]?))
    let origin (a : Nat) : String :=
      match gateOf a with
      | some (g, gate) => s!"assertion {a} (gate {g}: {gateName gate})"
      | none => s!"assertion {a}"
    let locate (site : ShareSite) : Option Located := do
      let trace ← trace
      let gate := (gateOf site.assertion).bind fun (g, _) ↦ trace.stackOfGate g
      match trace.stackOfRef site.node with
      | some built => return ⟨built, false, gate, site.operands.map trace.stackOfRef⟩
      | none => return ⟨← gate, true, gate, site.operands.map trace.stackOfRef⟩
    -- group sites with the same source; unlocated ones stay on their own
    let mut groups : Array (ShareSite × Option Located × Nat) := #[]
    for site in sites do
      let located := locate site
      match located, groups.findIdx? (fun (_, l, _) ↦ l.isSome && l == located) with
      | some _, some i => groups := groups.modify i fun (s, l, n) ↦ (s, l, n + 1)
      | _, _ => groups := groups.push (site, located, 1)
    let header := if sites.size == 1 then
        "1 node is not rank-1 and needs auxiliary witness variables. Share the listed operands:"
      else s!"{sites.size} nodes are not rank-1 and need auxiliary witness variables. \
        Share the listed operands:"
    let shown := groups.map fun (site, located, count) ↦
      match trace, located with
      | some trace, some located => site.renderLocated σ trace (gateOf site.assertion) located count
      | _, _ => site.render σ (origin site.assertion)
    return "\n".intercalate (#[header] ++ shown).toList

/-- `quadraticToR1CS` with a readable error. -/
def compileExplained (cs : ConstraintSystem p) (numPublic numPrivate numVars : Nat) :
    Except String (Compilation p) :=
  (quadraticToR1CS cs numPublic numPrivate numVars).mapError (·.render cs.σ)

/-! ## Checking a witness against the rows -/

/-- `Σ coefficient · w[wire] mod prime`; a wire outside `w` counts as 0 (`R1CSv1.validate` and
the witness length check rule that out). -/
def evalTerms (prime : Nat) (w : Array Nat) (terms : Array (UInt32 × Nat)) : Nat :=
  terms.foldl (fun acc (i, c) ↦ (acc + c * w[i.toNat]?.getD 0) % prime) 0

/-- The first row with (A·w)(B·w) ≠ C·w mod the prime, as (row, A·w, B·w, C·w). -/
def firstFailingRow (r : R1CSv1) (w : Array Nat) : Option (Nat × Nat × Nat × Nat) :=
  let p := r.header.prime
  r.constraints.zipIdx.findSome? fun (c, i) ↦
    let a := evalTerms p w c.termsA
    let b := evalTerms p w c.termsB
    let cv := evalTerms p w c.termsC
    if a * b % p == cv then none else some (i, a, b, cv)

/-- Why row `row` fails: its values, the assertion and gate behind it, and the source line that
emitted the gate. An eq0 row fails because the inputs do not satisfy the program; any other
gate's row means the witness generator gave that gate a wrong value. -/
def renderRowFailure (cs : ConstraintSystem p) (circuit : Circuit) (trace : Trace)
    (row a b c : Nat) : String :=
  let gates := if circuit.assertionGates.size == cs.eq0s.size then circuit.assertionGates else #[]
  let gate? : Option (Nat × Gate) := do
    let g ← gates[row]?
    return (g, ← circuit[g]?)
  let expr := match cs.eq0s[row]? with
    | some ref => s!"e{ref} := {renderExpr cs.σ ref}"
    | none => s!"row {row}"
  let head := s!"the witness does not satisfy row {row}: A·w = {a}, B·w = {b}, \
    (A·w)(B·w) = {a * b % p}, but C·w = {c} (mod {p})"
  let what := match gate? with
    | some (g, .eq0 _) => s!"• assertion {row} (gate {g}: eq0) is false for these inputs: {expr}"
    | some (g, gate) => s!"• assertion {row} (gate {g}: {gateName gate}) does not hold for the \
        values the witness generator gave the gate: {expr}"
    | none => s!"• assertion {row}: {expr}"
  let frame := (gate?.bind fun (g, _) ↦ trace.stackOfGate g).bind fun s ↦
    (frameLines (trace.frames s)).map (·.2)
  "\n".intercalate (#[head, what] ++ frame.getD #[]).toList

end Clap.ConstraintSystem

namespace Clap

open ConstraintSystem

/-- One run of the traced program on `numInputs` input slots: its trace, circuit and heap, and
the constraint system `toCs` makes of them. -/
private def runTraced {p : Nat} [Fact (Nat.Prime p)] (prog : ClapM p Unit) [HasTrace prog]
    (numInputs : Nat) : Trace × Circuit × HashConsSt p × ConstraintSystem p :=
  let ((((_, trace), circuit), _), σ) := (HasTrace.traced prog).run numInputs {}
  (trace, circuit, σ, circuit.toCs σ numInputs)

private def renderError {p : Nat} [Fact (Nat.Prime p)] (cs : ConstraintSystem p)
    (circuit : Circuit) (trace : Trace) (e : CompileError) : String :=
  let circuit? := if circuit.assertionGates.size == cs.eq0s.size then some circuit else none
  e.render cs.σ circuit? (trace := some trace)

/-- Compile a ClapM program to R1CS. The program's input slots are `numPublic` public inputs, then
`numPrivate` private ones, so the wires are `[ONE, public…, private…, internal…]`. On failure the
message names what to fix: for a `clap def` program, the source lines that built each offending
node and the value to share. -/
def compile {p : Nat} [Fact (Nat.Prime p)] (prog : ClapM p Unit) [HasTrace prog]
    (numPublic numPrivate : Nat) : Except String R1CSv1 :=
  let numInputs := numPublic + numPrivate
  let (trace, circuit, _, cs) := runTraced prog numInputs
  (toR1CS cs numPublic numPrivate (circuit.numVars numInputs)).mapError
    (renderError cs circuit trace)

/-- Compile `prog` and compute its witness for these inputs, from one run of the program. The
witness is `[1] ++ trace`, the trace is checked to fill `Circuit.numVars` slots, both files are
validated (`R1CSv1.validate`, `Witness.validate`), and every row (A·w)(B·w) = C·w is checked. The
first failing row is reported with its assertion, gate and source line. -/
def compileWithWitness {p : Nat} [Fact (Nat.Prime p)] (prog : ClapM p Unit) [HasTrace prog]
    (publicInputs privateInputs : Array (ZMod p)) : Except String (R1CSv1 × Witness) := do
  let inputs := publicInputs ++ privateInputs
  let (trace, circuit, σ, cs) := runTraced prog inputs.size
  let numVars := circuit.numVars inputs.size
  let compiled ← (quadraticToR1CS cs publicInputs.size privateInputs.size numVars).mapError
    (renderError cs circuit trace)
  let values ← (circuit.toWg σ inputs.size).run? inputs.toVector
  let witness ← (compiled.toWtns values).mapError fun _ ↦
    s!"the witness generator made {values.size} trace values, but the circuit has {numVars} \
      witness slots"
  let internal (what : String) (e : String) : String := s!"internal error, invalid {what}: {e}"
  compiled.r1cs.validate.mapError (internal "r1cs")
  witness.validate.mapError (internal "witness")
  let h := compiled.r1cs.header
  unless witness.prime == h.prime && witness.n8 == h.fieldElemSize && witness.nVars == h.nWires
      && witness.elements[0]? == some 1 do
    throw "internal error: the witness header does not match the r1cs header"
  if let some (row, a, b, c) := firstFailingRow compiled.r1cs witness.elements then
    throw (renderRowFailure cs circuit trace row a b c)
  return (compiled.r1cs, witness)

/-- `compileWithWitness`, then write `base.r1cs`, `base.wtns` and `base.sym` (the symbol file
`snarkjs r1cs print` loads; wire `i + 1` is named `main.v{i}`, trace slot `i` as in compile
errors). Returns 0. If compilation or a check fails, prints why, writes nothing and returns 1. -/
def writeR1CS {p : Nat} [Fact (Nat.Prime p)] (prog : ClapM p Unit) [HasTrace prog]
    (publicInputs privateInputs : Array (ZMod p)) (base : System.FilePath) : IO UInt32 := do
  match compileWithWitness prog publicInputs privateInputs with
  | .error message =>
    IO.eprintln message
    return 1
  | .ok (r1cs, witness) =>
    serializeR1CS (base.addExtension "r1cs") r1cs
    Witness.serializeWitness (base.addExtension "wtns") witness
    serializeSym (base.addExtension "sym") (r1cs.header.nWires.toNat - 1) (s!"main.v{·}")
    return 0

end Clap
