import Clap.Compiler.Compile
import Clap.Test.R1CS.Lowering
import Clap.Test.R1CS.Remap
import Clap.Test.R1CS.Witness

/-!
# ClapM programs through the whole pipeline
-/

namespace Clap.Test.R1CS

open HashConsM
open Clap.ConstraintSystem
open Clap.Serialize

/-! ## Handcrafted ClapM circuits: follow the complete compilation pipeline

Every program starts with three original input slots x,y,z. The definitions
below spell out ClapM → Circuit → ConstraintSystem → normalization → R1CS.
Witnesses additionally run Circuit.toWg and Compilation.toWtns.
t,u,v name the extra trace slots that gates allocate (share, num2bits, isZero).
 `compile` rejects a program that needs a share it does not have.
For a `clap def` program, its message points at the source lines to fix.
-/

namespace Pipeline

open Lean Elab Term in
/-- The line this term is written on. Expected messages count lines from such markers, so
edits elsewhere in this file do not change them. -/
local elab "currentLine%" : term => do
  return mkNatLit ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line

-- Assert x+y=z.
def linearProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let sum ← x + y
  eq0 (← sum - z)

-- Assert xy=z, already a single R1CS row.
def productProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let product ← x * y
  eq0 (← product - z)

-- Assert xyz=3 WITHOUT share the compiler rejects it.
def cubicLine : Nat := currentLine%
clap def cubicProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let xy ← x * y
  let xyz ← xy * z
  let three ← liftM (mkConstant (p := 7) 3)
  eq0 (← xyz - three)

-- The same assertion WITH share the source witness contains t=xy.
def sharedLine : Nat := currentLine%
clap def sharedProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let xy ← x * y
  let t ← share xy
  let xyz ← t * z
  let three ← liftM (mkConstant (p := 7) 3)
  eq0 (← xyz - three)

-- The cubic again, as a plain `def` no source lines, but the gate is still named.
def plainCubicProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let xy ← x * y
  let xyz ← xy * z
  let three ← liftM (mkConstant (p := 7) 3)
  eq0 (← xyz - three)

-- Assert xy+yz-zx=0 WITHOUT share two products too many for one row.
def dotLine : Nat := currentLine%
clap def dotProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let xy ← x * y
  let yz ← y * z
  let zx ← z * x
  eq0 (← (← xy + yz) - zx)

-- The fix the error suggests share yz (t) and zx (u).
clap def dotSharedProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let xy ← x * y
  let yz ← share (← y * z)
  let zx ← share (← z * x)
  eq0 (← (← xy + yz) - zx)

-- Each share reads the previous one t=xy, u=tz, v=ux; then assert v=y, i.e. x²z=1.
def chainLine : Nat := currentLine%
clap def chainProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let z ← liftM (mkVar (p := 7) 2)
  let t ← share (← x * y)
  let u ← share (← t * z)
  let v ← share (← u * x)
  eq0 (← v - y)

-- A helper that multiplies three values, and a program calling it the message follows the
-- call from the helper's line to the caller's.
def mulThreeLine : Nat := currentLine%
clap def mulThree (a b c : BoundRef 7) : ClapM 7 (BoundRef 7) := do
  let ab ← a * b
  ab * c

clap def mulThreeCaller : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let r ← mulThree x y x
  eq0 r

-- A loop that builds the same kind of non-rank-1 product twice shown once, with the count.
def loopLine : Nat := currentLine%
clap def loopProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  for i in [0:2] do
    let c ← liftM (mkConstant (p := 7) (i + 2))
    let s ← x * c
    let sq ← s * x
    eq0 (← sq * x)

-- `loopProgram` with `loopRange` whose traced copy loops in `LocatedM`.
def loopRangeLine : Nat := currentLine%
clap def loopRangeProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  for i in loopRange 2 do
    let c ← liftM (mkConstant (p := 7) (i + 2))
    let s ← x * c
    let sq ← s * x
    eq0 (← sq * x)

-- Decompose x into three Boolean digits t,u,v, least-significant bit first.
def bitsProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let _ ← num2bits 3 x
  pure ()

-- isZero introduces an inverse hint t and a flag u assert u=1, hence x=y.
def isZeroProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let difference ← x - y
  let flag ← isZero difference
  let one ← liftM (mkConstant (p := 7) 1)
  eq0 (← flag - one)

-- isZero of a product the gadget multiplies its argument by the inverse hint t.
def isZeroLine : Nat := currentLine%
clap def isZeroOfProductProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let flag ← isZero (← x * y)
  let one ← liftM (mkConstant (p := 7) 1)
  eq0 (← flag - one)

-- The fix: share xy (t) first isZero then adds the inverse hint u and the flag v.
def isZeroSharedProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let y ← liftM (mkVar (p := 7) 1)
  let xy ← share (← x * y)
  let flag ← isZero xy
  let one ← liftM (mkConstant (p := 7) 1)
  eq0 (← flag - one)

-- These are thin views of the actual stages, not another implementation of them.
def circuitOf (program : ClapM 7 Unit) := program.getCircuit 3 {}
def constraintsOf (program : ClapM 7 Unit) := (circuitOf program).toCs (program.getHashConsState 3 {}) 3
def sourceWitnessOf (program : ClapM 7 Unit) (inputs : Vector (ZMod 7) 3) := ((circuitOf program).toWg (program.getHashConsState 3 {}) 3).run inputs
def compileProgram (program : ClapM 7 Unit) (inputs : Vector (ZMod 7) 3) := (constraintsOf program).quadraticToR1CS 3 0 (sourceWitnessOf program inputs).size

def normalizationOf (program : ClapM 7 Unit) (numVars : Nat) : Option (QuadraticSt 7) :=
  let cs := constraintsOf program
  (cs.eq0s.zipIdx.forM fun (ref, i) => normalQuadratic numVars cs.σ i ref).run {} |>.toOption.map Prod.snd

def exportedRows (program : ClapM 7 Unit) (inputs : Vector (ZMod 7) 3) := (compileProgram program inputs).toOption.map (·.r1cs.constraints)
def serializedWitness (program : ClapM 7 Unit) (inputs : Vector (ZMod 7) 3) : Option (Array Nat) := do
  let compilation ← (compileProgram program inputs).toOption
  return (← (compilation.toWtns (sourceWitnessOf program inputs)).toOption).elements

/-- The `compile` error message for `program` with three inputs, or "ok". -/
def compiledMessage (program : ClapM 7 Unit) [HasTrace program] : String :=
  match compile program 3 0 with
  | .error message => message
  | .ok _ => "ok"

private def file : String := "Clap/Test/R1CS/Pipeline.lean"

def needHeader (n : Nat) : String :=
  if n == 1 then
    "1 node is not rank-1 and needs auxiliary witness variables. Share the listed operands:"
  else s!"{n} nodes are not rank-1 and need auxiliary witness variables. \
    Share the listed operands:"

/-- The source frame `compile` prints for a site at `line:col` in `decl`, then its notes. -/
def framed (line col : Nat) (decl text : String) (notes : List String) : List String :=
  let pad := "".pushn ' ' ((toString line).length + 1)
  [s!"{pad}┌─ {file}:{line}:{col} in {decl}", s!"{line} │ {text}"] ++ notes.map (pad ++ "= " ++ ·)

-- Compare the already exported rows with independently written linear expressions.
def hasRows (numWires : Nat) (actual : Option Constraints) (expected : Array (TestExpr × TestExpr × TestExpr)) : Bool :=
  match actual, expected.mapM (expectedRow numWires) with
  | some actual, some expected => actual == expected
  | _, _ => false

-- x+y=z: one gate, one zero assertion, one linear row, and no additional values.
example : (circuitOf linearProgram).map gateName == #["eq0"] := by native_decide
example : (constraintsOf linearProgram).eq0s.size == 1 := by native_decide
example : (sourceWitnessOf linearProgram #v[2,3,5]) == #[2,3,5] := by native_decide
example : (normalizationOf linearProgram 3).map (fun s => (s.rows.size, s.sites.size)) == some (1,0) := by native_decide
example : hasRows 4 (exportedRows linearProgram #v[2,3,5]) #[(x+y-z, 1, 0)] := by native_decide
example : serializedWitness linearProgram #v[2,3,5] == some #[1,2,3,5] := by native_decide

-- xy=z one existing quadratic, no share needed.
example : (circuitOf productProgram).map gateName == #["eq0"] := by native_decide
example : (constraintsOf productProgram).eq0s.size == 1 := by native_decide
example : (normalizationOf productProgram 3).map (fun s => (s.rows.size, s.sites.size)) == some (1,0) := by native_decide
example : hasRows 4 (exportedRows productProgram #v[2,3,6]) #[(x,y,z)] := by native_decide
example : serializedWitness productProgram #v[2,3,6] == some #[1,2,3,6] := by native_decide

-- xyz=3 without share one assertion, one site, nothing exported.
example : (circuitOf cubicProgram).map gateName == #["eq0"] := by native_decide
example : (constraintsOf cubicProgram).eq0s.size == 1 := by native_decide
example : sourceWitnessOf cubicProgram #v[2,3,4] == #[2,3,4] := by native_decide
example : (normalizationOf cubicProgram 3).map (fun s => (s.rows.size, s.sites.size)) == some (1,1) := by native_decide
example : (exportedRows cubicProgram #v[2,3,4]).isNone := by native_decide
example : serializedWitness cubicProgram #v[2,3,4] == none := by native_decide
example : compiledMessage cubicProgram == lines ([needHeader 1,
    "• product with a quadratic factor: e4 := v0 * v1 * v2"] ++
    framed (cubicLine + 6) 2 "cubicProgram" "let xyz ← xy * z" [
      s!"gate 0 (eq0) emitted at {file}:{cubicLine + 8}:2: eq0 (← xyz - three)",
      s!"share e3 := v0 * v1, built at {file}:{cubicLine + 5}:2: let xy ← x * y"]) := by native_decide
-- The plain `def` gets the same site, located by assertion and gate only.
example : compiledMessage plainCubicProgram == lines [needHeader 1,
    "• assertion 0 (gate 0: eq0): product with a quadratic factor",
    "    e4 := v0 * v1 * v2",
    "  share e3 := v0 * v1"] := by native_decide

-- With share 2*3*4=3 modulo 7. The share gate supplies t=6 and its row xy=t.
example : (circuitOf sharedProgram).map gateName == #["share","eq0"] := by native_decide
example : (constraintsOf sharedProgram).eq0s.size == 2 := by native_decide
example : sourceWitnessOf sharedProgram #v[2,3,4] == #[2,3,4,6] := by native_decide
example : (normalizationOf sharedProgram 4).map (fun s => (s.rows.size, s.sites.size)) == some (2,0) := by native_decide
example : hasRows 5 (exportedRows sharedProgram #v[2,3,4]) #[(x,y,t), (t,z,3)] := by native_decide
example : serializedWitness sharedProgram #v[2,3,4] == some #[1,2,3,4,6] := by native_decide
example : compiledMessage sharedProgram == "ok" := by native_decide
example : (compile sharedProgram 3 0).toOption.map (·.constraints) == exportedRows sharedProgram #v[2,3,4] := by native_decide

-- xy+yz-zx without share two sites in one assertion, each with two alternatives.
example : compiledMessage dotProgram == lines ([needHeader 2,
    "• sum of two quadratics: e6 := v0 * v1 + v1 * v2"] ++
    framed (dotLine + 8) 12 "dotProgram" "xy + yz" [
      s!"gate 0 (eq0) emitted at {file}:{dotLine + 8}:2: eq0 (← (← xy + yz) - zx)",
      s!"share e4 := v1 * v2, built at {file}:{dotLine + 6}:2: let yz ← y * z",
      s!"or    e3 := v0 * v1, built at {file}:{dotLine + 5}:2: let xy ← x * y"] ++
    ["• difference of two quadratics: e7 := v0 * v1 + v1 * v2 - v2 * v0"] ++
    framed (dotLine + 8) 9 "dotProgram" "(← xy + yz) - zx" [
      s!"gate 0 (eq0) emitted at {file}:{dotLine + 8}:2: eq0 (← (← xy + yz) - zx)",
      s!"share e5 := v2 * v0, built at {file}:{dotLine + 7}:2: let zx ← z * x",
      s!"or    e6 := v0 * v1 + v1 * v2, built at {file}:{dotLine + 8}:12: xy + yz"]) := by native_decide

-- Sharing the first suggestion of each site (yz=t, zx=u) gives one row per gate.
-- At [2,3,4], t=12=5 and u=8=1 modulo 7.
example : (circuitOf dotSharedProgram).map gateName == #["share","share","eq0"] := by native_decide
example : hasRows 6 (exportedRows dotSharedProgram #v[2,3,4]) #[(y,z,t), (z,x,u), (x,y,u-t)] := by native_decide
example : serializedWitness dotSharedProgram #v[2,3,4] == some #[1,2,3,4,5,1] := by native_decide
example : (compile dotSharedProgram 3 0).toOption.map (·.constraints) == exportedRows dotSharedProgram #v[2,3,4] := by native_decide

-- The product is built in the helper the message also shows the call.
example : compiledMessage mulThreeCaller == lines ([needHeader 1,
    "• product with a quadratic factor: e3 := v0 * v1 * v0"] ++
    framed (mulThreeLine + 3) 2 "mulThree" "ab * c" [
      s!"called from {file}:{mulThreeLine + 8}:2 in mulThreeCaller: let r ← mulThree x y x",
      s!"gate 0 (eq0) emitted at {file}:{mulThreeLine + 9}:2: eq0 r",
      s!"share e2 := v0 * v1, built at {file}:{mulThreeLine + 2}:2: let ab ← a * b"]) := by native_decide

-- Both iterations have the same source lines, so the two sites are shown once.
example : compiledMessage loopProgram == lines ([needHeader 2,
    "• product with a quadratic factor (2 times): e4 := v0 * 2 * v0 * v0"] ++
    framed (loopLine + 7) 11 "loopProgram" "sq * x" [
      s!"gate 0 (eq0) emitted at {file}:{loopLine + 7}:4: eq0 (← sq * x)",
      s!"share e3 := v0 * 2 * v0, built at {file}:{loopLine + 6}:4: let sq ← s * x"]) := by native_decide

-- With `loopRange` the same heap and gates, and the same sites, inside the loop body.
example : (loopRangeProgram.getHashConsState 3 {}).exprs == (loopProgram.getHashConsState 3 {}).exprs &&
    (circuitOf loopRangeProgram).map gateName == (circuitOf loopProgram).map gateName := by
  native_decide
example : compiledMessage loopRangeProgram == lines ([needHeader 2,
    "• product with a quadratic factor (2 times): e4 := v0 * 2 * v0 * v0"] ++
    framed (loopRangeLine + 7) 11 "loopRangeProgram" "sq * x" [
      s!"gate 0 (eq0) emitted at {file}:{loopRangeLine + 7}:4: eq0 (← sq * x)",
      s!"share e3 := v0 * 2 * v0, built at {file}:{loopRangeLine + 6}:4: let sq ← s * x"]) := by
  native_decide

-- 5=1+2*0+4*1. The gate supplies t,u,v=[1,0,1] all four rows are already R1CS.
example : (circuitOf bitsProgram).map gateName == #["num2bits 3"] := by native_decide
example : (constraintsOf bitsProgram).eq0s.size == 4 := by native_decide
example : sourceWitnessOf bitsProgram #v[5,0,0] == #[5,0,0,1,0,1] := by native_decide
example : (normalizationOf bitsProgram 6).map (fun s => (s.rows.size, s.sites.size)) == some (4,0) := by native_decide
example : hasRows 7 (exportedRows bitsProgram #v[5,0,0]) #[(t,1-t,0), (u,1-u,0), (v,1-v,0), (t+2*u+4*v-x,1,0)] := by native_decide
example : serializedWitness bitsProgram #v[5,0,0] == some #[1,5,0,0,1,0,1] := by native_decide
-- Non-palindromic bit patterns distinguish least-significant-first from reversed order.
example : sourceWitnessOf bitsProgram #v[3,0,0] == #[3,0,0,1,1,0] := by native_decide
example : serializedWitness bitsProgram #v[6,0,0] == some #[1,6,0,0,0,1,1] := by native_decide

-- For x=y=2, isZero supplies t=0 and u=1. The third source slot is unused.
example : (circuitOf isZeroProgram).map gateName == #["isZero","eq0"] := by native_decide
example : (constraintsOf isZeroProgram).eq0s.size == 3 := by native_decide
example : sourceWitnessOf isZeroProgram #v[2,2,0] == #[2,2,0,0,1] := by native_decide
example : (normalizationOf isZeroProgram 5).map (fun s => (s.rows.size, s.sites.size)) == some (3,0) := by native_decide
example : hasRows 6 (exportedRows isZeroProgram #v[2,2,0]) #[(-t,x-y,u-1), (u,x-y,0), (u-1,1,0)] := by native_decide
example : serializedWitness isZeroProgram #v[2,2,0] == some #[1,2,2,0,0,1] := by native_decide

-- isZero of xy assertions 0-1 are the isZero rows and 2 is the eq0. The first isZero row
-- multiplies the inverse hint (v3) by xy. That node belongs to the gate, so the message points
-- at the line emitting it. The second row reuses xy, already reported: one site.
example : (circuitOf isZeroOfProductProgram).assertionGates == #[0, 0, 1] := by native_decide
example : compiledMessage isZeroOfProductProgram == lines ([needHeader 1,
    "• product with a quadratic factor: e7 := v3 * (v0 * v1)"] ++
    framed (isZeroLine + 4) 2 "isZeroOfProductProgram" "let flag ← isZero (← x * y)" [
      "the node is part of gate 0 (isZero), which this line emits",
      s!"share e2 := v0 * v1, built at {file}:{isZeroLine + 4}:23: x * y"]) := by native_decide

-- With xy shared as t, isZero's hint is u and its flag v. The witness generator fills its
-- expression cache gate by gate, so isZero can read the share output t (below).
example : (circuitOf isZeroSharedProgram).map gateName == #["share","isZero","eq0"] := by native_decide
example : hasRows 7 (((constraintsOf isZeroSharedProgram).quadraticToR1CS 3 0 6).toOption.map (·.r1cs.constraints))
    #[(x,y,t), (-u,t,v-1), (v,t,0), (v-1,1,0)] := by native_decide

-- `compile` counts the witness slots from the gates; they match the witness generator's trace.
example : (circuitOf bitsProgram).numVars 3 == (sourceWitnessOf bitsProgram #v[5,0,0]).size := by native_decide
example : (circuitOf isZeroProgram).numVars 3 == (sourceWitnessOf isZeroProgram #v[2,2,0]).size := by native_decide
example : (circuitOf sharedProgram).numVars 3 == (sourceWitnessOf sharedProgram #v[2,3,4]).size := by native_decide
example : (circuitOf dotSharedProgram).numVars 3 == (sourceWitnessOf dotSharedProgram #v[2,3,4]).size := by native_decide

/-! ### Witnesses: `compileWithWitness` checks every row

It runs the program once for both the rows and the witness, and reports the first row the
witness does not satisfy, with its assertion, gate and source line. -/

def witnessOf (program : ClapM 7 Unit) [HasTrace program] (pub prv : Array (ZMod 7)) :
    Option (Array Nat) :=
  (compileWithWitness program pub prv).toOption.map (·.2.elements)

def witnessError {p : Nat} [Fact (Nat.Prime p)] (program : ClapM p Unit) [HasTrace program]
    (pub prv : Array (ZMod p)) : String :=
  match compileWithWitness program pub prv with
  | .error message => message
  | .ok _ => "ok"

-- Satisfying inputs the witness is ONE, then the trace.
example : witnessOf sharedProgram #[2,3,4] #[] == some #[1,2,3,4,6] := by native_decide
-- xy+yz=zx holds at x=1, y=3, z=2 (3+6=2 mod 7), with yz=6 and zx=2.
example : witnessOf dotSharedProgram #[1,3,2] #[] == some #[1,1,3,2,6,2] := by native_decide
example : witnessOf bitsProgram #[5,0,0] #[] == some #[1,5,0,0,1,0,1] := by native_decide
example : witnessOf isZeroProgram #[2,2,0] #[] == some #[1,2,2,0,0,1] := by native_decide

-- Gates that read earlier gates' outputs. chainProgram: x²z=1 at x=2, z=2, with t=6, u=12=5 and
-- v=10=3=y. isZero of the share output t at xy=6 the hint is 6⁻¹=6 and the flag 0 at xy=0
-- the hint is 0 and the flag 1.
example : witnessOf chainProgram #[2,3,2] #[] == some #[1,2,3,2,6,5,3] := by native_decide
example : sourceWitnessOf isZeroSharedProgram #v[2,3,0] == #[2,3,0,6,6,0] := by native_decide
example : witnessOf isZeroSharedProgram #[0,3,0] #[] == some #[1,0,3,0,0,0,1] := by native_decide

-- One public input and two private ones the same wires, split in the header.
example : (compileWithWitness sharedProgram #[2] #[3,4]).toOption.map
    (fun (r, w) => (r.header.nPubIn, r.header.nPrvIn, w.elements)) == some (1, 2, #[1,2,3,4,6]) := by
  native_decide
example : (compile sharedProgram 1 2).toOption.map (fun r => (r.header.nPubIn, r.header.nPrvIn)) ==
    some (1, 2) := by native_decide

-- Inputs that do not satisfy the program the first false row, its assertion and source line.
-- 2*3*5 = 2, not 3, modulo 7.
example : witnessError sharedProgram #[2,3,5] #[] == lines ([
    "the witness does not satisfy row 1: A·w = 6, B·w = 5, (A·w)(B·w) = 2, but C·w = 3 (mod 7)",
    "• assertion 1 (gate 1: eq0) is false for these inputs: e7 := v3 * v2 - 3"] ++
    framed (sharedLine + 9) 2 "sharedProgram" "eq0 (← xyz - three)" []) := by native_decide
-- The inputs of the dotSharedProgram row tests above do not satisfy it 6+12-8 = 3.
example : witnessError dotSharedProgram #[2,3,4] #[] == lines ([
    "the witness does not satisfy row 2: A·w = 2, B·w = 3, (A·w)(B·w) = 6, but C·w = 3 (mod 7)",
    "• assertion 2 (gate 2: eq0) is false for these inputs: e9 := v0 * v1 + v3 - v4"] ++
    framed (dotLine + 18) 2 "dotSharedProgram" "eq0 (← (← xy + yz) - zx)" []) := by native_decide
-- x²z = 16 = 2, not 1 v = 6, not y = 3.
example : witnessError chainProgram #[2,3,4] #[] == lines ([
    "the witness does not satisfy row 3: A·w = 3, B·w = 1, (A·w)(B·w) = 3, but C·w = 0 (mod 7)",
    "• assertion 3 (gate 3: eq0) is false for these inputs: e9 := v5 - v1"] ++
    framed (chainLine + 8) 2 "chainProgram" "eq0 (← v - y)" []) := by native_decide
-- A plain `def` has no source line. xy=6 is not zero, so the flag is 0 and flag=1 fails.
example : witnessError isZeroSharedProgram #[2,3,0] #[] == lines [
    "the witness does not satisfy row 3: A·w = 6, B·w = 1, (A·w)(B·w) = 6, but C·w = 0 (mod 7)",
    "• assertion 3 (gate 2: eq0) is false for these inputs: e6 := v5 - 1"] := by native_decide
-- A program that needs a share fails as in `compile`.
example : witnessError cubicProgram #[2,3,4] #[] == compiledMessage cubicProgram := by native_decide
example : witnessOf cubicProgram #[1,1,3] #[] == none := by native_decide

/-! ### Variables to trace slots -/

def remapPrograms : List (ClapM 7 Unit) :=
  [sharedProgram, dotSharedProgram, chainProgram, bitsProgram, isZeroProgram, isZeroSharedProgram]

example : remapPrograms.all (Remap.remapsAgree ∘ circuitOf) := by native_decide
-- The whole remapped heap, too.
example : remapPrograms.all fun program ↦
    let σ := program.getHashConsState 3 {}
    (offsetHashConsState 3 σ (circuitOf program)).exprs ==
      (offsetHashConsStateRef 3 σ (circuitOf program)).exprs := by
  native_decide

/-! ### fpmul

A program with one fpmul gate -/

private instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

-- r = a·b mod p' on two 4-bit limbs, then gates that read r: a share of r₀·x, and r = (r₀', r₁')
-- limb by limb. Inputs a₀ a₁ b₀ b₁ p'₀ p'₁ r₀' r₁' x.
def fpmulLine : Nat := currentLine%
clap def fpmulProgram : ClapM 65537 Unit := do
  let a0 ← liftM (mkVar (p := 65537) 0)
  let a1 ← liftM (mkVar (p := 65537) 1)
  let b0 ← liftM (mkVar (p := 65537) 2)
  let b1 ← liftM (mkVar (p := 65537) 3)
  let m0 ← liftM (mkVar (p := 65537) 4)
  let m1 ← liftM (mkVar (p := 65537) 5)
  let r0' ← liftM (mkVar (p := 65537) 6)
  let r1' ← liftM (mkVar (p := 65537) 7)
  let x ← liftM (mkVar (p := 65537) 8)
  let r ← fpmul 4 2 #v[a0, a1] #v[b0, b1] #v[m0, m1]
  let _ ← share (← r[0] * x)
  eq0 (← r[0] - r0')
  eq0 (← r[1] - r1')

-- 200·150 = 30000 = 119·251 + 131, and 131 = 3 + 8·16: a = (8,12), b = (6,9), p' = (11,15).
def fpmulInputs (r0 : ZMod 65537) : Array (ZMod 65537) := #[8, 12, 6, 9, 11, 15, r0, 8]

/-- The witness values at the wires of the ClapM variables `vars` (past the 9 inputs) wire
`1 + 9 + offsetIdx circuit v`. -/
def fpmulWitnessAt (vars : List ℕ) : Option (List ℕ) := do
  let (_, w) ← (compileWithWitness fpmulProgram (fpmulInputs 3) #[5]).toOption
  let circuit := fpmulProgram.getCircuit 9 {}
  vars.mapM fun v ↦ w.elements[1 + 9 + offsetIdx circuit v]?

-- Every row holds, r is (3, 8) = a·b mod p', and the share after fpmul (variable 2) is r₀·x = 15.
example : fpmulWitnessAt [0, 1, 2] == some [3, 8, 15] := by native_decide
-- r₀' = 4 ≠ r₀: the eq0 row fails, and it reads r₀ at slot 9 + 37 = 46.
example : witnessError fpmulProgram (fpmulInputs 4) #[5] == lines ([
    "the witness does not satisfy row 95: A·w = 65536, B·w = 1, (A·w)(B·w) = 65536, but C·w = 0 (mod 65537)",
    "• assertion 95 (gate 2: eq0) is false for these inputs: e13 := v46 - v6"] ++
    framed (fpmulLine + 13) 2 "fpmulProgram" "eq0 (← r[0] - r0')" []) := by native_decide

-- Every k exports: `check_lt` shares its running flag (Clap/Model/ConstraintSystem/fpMul.lean).
example : (compile (Witness.fpmulK 2) 6 0).toOption.isSome := by native_decide
example : (compile (Witness.fpmulK 3) 9 0).toOption.isSome := by native_decide
example : (compile (Witness.fpmulK 4) 12 0).toOption.isSome := by native_decide
-- `toCs` pushes `gateAssertions` rows per gate (they locate a row's gate in `compile`'s messages).
example : [1, 2, 3, 4].all fun k ↦
    let circuit := (Witness.fpmulK k).getCircuit (3 * k) {}
    (circuit.toCs ((Witness.fpmulK k).getHashConsState (3 * k) {}) (3 * k)).eq0s.size ==
      (circuit.map gateAssertions).sum := by native_decide

/-! ### Gate outputs are `BoundRef p`

`u * u` on two share outputs builds a heap node with a forgotten `←` it is a type error, not ℕ
multiplication of heap indices. -/

def squareShareProgram : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let u ← share x
  let v ← share (← u * u)
  eq0 v

example : (match (circuitOf squareShareProgram)[1]? with
    | some (Gate.share e) => renderExpr (squareShareProgram.getHashConsState 3 {}) e
    | _ => "") == "v3 * v3" := by native_decide

/-! ### Source paths

Frames name the module's file with its components unescaped. -/

example : ClapDef.moduleFile `scripts.«emit-r1cs» == "scripts/emit-r1cs.lean" := by native_decide
example : ClapDef.moduleFile `Clap.Test.R1CS.Pipeline == file := by native_decide

end Pipeline

end Clap.Test.R1CS
