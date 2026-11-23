import Clap.Compiler.toR1CS

/-!
# The R1CS lowering

`quadraticToR1CS` on constraint systems built from small arithmetic expressions over `ZMod 7`:
the rows it returns, or its error.
-/

namespace Clap.Test.R1CS

open HashConsM
open Clap.ConstraintSystem
open Clap.Serialize

/-! Small helpers for the arithmetic notation used by the examples below. -/

inductive TestExpr where
  | v (index : Nat)
  | c (value : ZMod 7)
  | add (left right : TestExpr)
  | sub (left right : TestExpr)
  | mul (left right : TestExpr)

instance : Add TestExpr := ⟨.add⟩
instance : Sub TestExpr := ⟨.sub⟩
instance : Mul TestExpr := ⟨.mul⟩
instance : Neg TestExpr := ⟨fun e => .sub (.c 0) e⟩
instance {n : Nat} : OfNat TestExpr n := ⟨.c n⟩

def x : TestExpr := .v 0
def y : TestExpr := .v 1
def z : TestExpr := .v 2
def t : TestExpr := .v 3
def u : TestExpr := .v 4
def v : TestExpr := .v 5
def w : TestExpr := .v 6

def TestExpr.build : TestExpr → HashConsM 7 (BoundRef 7)
  | .v i => mkVar i
  | .c k => mkConstant k
  | .add a b => do mkAdd (← a.build) (← b.build)
  | .sub a b => do mkSub (← a.build) (← b.build)
  | .mul a b => do mkMul (← a.build) (← b.build)

def sourceOf (inputs : Array TestExpr) : ConstraintSystem 7 :=
  let (roots, σ) := (inputs.mapM TestExpr.build).run (HashConsSt.empty 7)
  ⟨roots, σ⟩

/-- Convert an expected linear expression into a dense vector, including the
constant at wire zero. Expected products must have a literal constant factor;
nonlinear row sides and out-of-range variables are rejected. -/
def linearCoefficients (numWires : Nat) :
    TestExpr → Option (Vector (ZMod 7) numWires)
  | .c k =>
    if numWires == 0 then none
    else some (Vector.ofFn fun i => if i.val == 0 then k else 0)
  | .v j =>
    if j + 1 < numWires then
      some (Vector.ofFn fun i => if i.val == j + 1 then 1 else 0)
    else none
  | .add a b => do
    return (← linearCoefficients numWires a).zipWith (· + ·) (← linearCoefficients numWires b)
  | .sub a b => do
    return (← linearCoefficients numWires a).zipWith (· - ·) (← linearCoefficients numWires b)
  | .mul (.c k) b => do
    return (← linearCoefficients numWires b).map (k * ·)
  | .mul a (.c k) => do
    return (← linearCoefficients numWires a).map (· * k)
  | .mul _ _ => none

def expectedTerms (numWires : Nat) (e : TestExpr) :
    Option (Array (UInt32 × Nat)) := do
  let coefficients ← linearCoefficients numWires e
  return coefficients.toArray.zipIdx.filterMap fun (coefficient, wire) =>
    if coefficient == 0 then none else some (UInt32.ofNat wire, coefficient.val)

def expectedRow (numWires : Nat) (row : TestExpr × TestExpr × TestExpr) :
    Option Constraint := do
  let a ← expectedTerms numWires row.1
  let b ← expectedTerms numWires row.2.1
  let c ← expectedTerms numWires row.2.2
  return ⟨UInt32.ofNat a.size, UInt32.ofNat b.size, UInt32.ofNat c.size, a, b, c⟩

/-- Check successful compilation and exact equality of all ordered rows.
A failed compilation or invalid expected row never counts as a match.
x,y,z are the three public slots; `numVars` adds private slots t,u,v,w, which the
examples use for values a gadget would `share`. -/
def reducesAllTo (inputs : Array TestExpr) (expected : Array (TestExpr × TestExpr × TestExpr))
    (numVars : Nat := 3) : Bool :=
  let cs := sourceOf inputs
  match cs.quadraticToR1CS 3 0 numVars with
  | .error _ => false
  | .ok compiled =>
    match expected.mapM (expectedRow compiled.r1cs.header.nWires.toNat) with
    | none => false
    | some rows => compiled.r1cs.constraints == rows

def reducesTo (input : TestExpr) (expected : Array (TestExpr × TestExpr × TestExpr)) : Bool :=
  reducesAllTo #[input] expected

def lines (ls : List String) : String := "\n".intercalate ls

def errorOf {α : Type} : Except CompileError α → Option CompileError
  | .error e => some e
  | .ok _ => none

/-! ## Each expression is asserted equal to zero -/

-- Constant assertions remain rows: 0=0 is satisfiable; 1=0 is contradictory.
example : reducesTo 0 #[(0, 1, 0)] := by native_decide
example : reducesTo 1 #[(1, 1, 0)] := by native_decide

-- Linear expressions become L * 1 = 0; keep both subtraction signs correct.
example : reducesTo (x + (y - z)) #[(x + y - z, 1, 0)] := by native_decide
example : reducesTo ((x - y) - z) #[(x - y - z, 1, 0)] := by native_decide
example : reducesTo (3 * (x + y) - z) #[(3*x + 3*y - z, 1, 0)] := by native_decide
example : reducesTo (2*x + 5*x) #[(0, 1, 0)] := by native_decide -- 2+5=0 in ZMod 7.

-- These expressions already fit one quadratic row.
example : reducesTo (x * y - z) #[(x, y, z)] := by native_decide
example : reducesTo (z - x * y) #[(-x, y, -z)] := by native_decide
example : reducesTo (x * y + z) #[(x, y, -z)] := by native_decide

/-! ## incorrect -/

example : reducesTo (x*y-z) #[(x, y, -z)] = false := by native_decide -- Wrong sign.
example : reducesTo (x*y) #[(x*y, 1, 0)] = false := by native_decide -- A must be linear.
example : reducesTo t #[(t, 1, 0)] = false := by native_decide -- t is not a source input.

/-! ## Constants and field arithmetic -/

-- Canonical residues are modulo 7, including negative constants.
example : reducesTo 7 #[(0, 1, 0)] := by native_decide
example : reducesTo 8 #[(1, 1, 0)] := by native_decide
example : reducesTo (-1) #[(6, 1, 0)] := by native_decide
example : reducesTo (3+5) #[(1, 1, 0)] := by native_decide
example : reducesTo (2*3+1) #[(0, 1, 0)] := by native_decide
example : reducesTo (2-5) #[(4, 1, 0)] := by native_decide
example : reducesTo ((4-2)*(3+1)) #[(1, 1, 0)] := by native_decide

/-! ## Linear identities, nested signs, and coefficient cancellation -/

example : reducesTo x #[(x, 1, 0)] := by native_decide
example : reducesTo y #[(y, 1, 0)] := by native_decide
example : reducesTo z #[(z, 1, 0)] := by native_decide
example : reducesTo (x+0) #[(x, 1, 0)] := by native_decide
example : reducesTo (0+x) #[(x, 1, 0)] := by native_decide
example : reducesTo (x-0) #[(x, 1, 0)] := by native_decide
example : reducesTo (0-x) #[(-x, 1, 0)] := by native_decide
example : reducesTo (-(-x)) #[(x, 1, 0)] := by native_decide
example : reducesTo (x-x) #[(0, 1, 0)] := by native_decide
example : reducesTo ((x+y)-(y+x)) #[(0, 1, 0)] := by native_decide
example : reducesTo (x-(y-z)) #[(x-y+z, 1, 0)] := by native_decide
example : reducesTo ((x-y)+z) #[(x-y+z, 1, 0)] := by native_decide
example : reducesTo ((x+y)-x) #[(y, 1, 0)] := by native_decide
example : reducesTo (x+(y-x)) #[(y, 1, 0)] := by native_decide
example : reducesTo ((x-y)-(z-x)) #[(2*x-y-z, 1, 0)] := by native_decide
example : reducesTo ((2*x+3*y)-(4*x+y)) #[(5*x+2*y, 1, 0)] := by native_decide
example : reducesTo ((2*x+5*x)+z) #[(z, 1, 0)] := by native_decide

-- A scalar can be on either side or itself be a constant expression.
example : reducesTo (x*0) #[(0, 1, 0)] := by native_decide
example : reducesTo (0*x) #[(0, 1, 0)] := by native_decide
example : reducesTo (x*1) #[(x, 1, 0)] := by native_decide
example : reducesTo (1*x) #[(x, 1, 0)] := by native_decide
example : reducesTo (x*7) #[(0, 1, 0)] := by native_decide
example : reducesTo (2*(3*x)) #[(6*x, 1, 0)] := by native_decide
example : reducesTo ((x*3)*2) #[(6*x, 1, 0)] := by native_decide
example : reducesTo ((2+3)*x) #[(5*x, 1, 0)] := by native_decide
example : reducesTo ((3-3)*(x+y)) #[(0, 1, 0)] := by native_decide
example : reducesTo (2*(x-(y+z))) #[(2*x-2*y-2*z, 1, 0)] := by native_decide
example : reducesTo ((x+y)*3-(2*x+z)) #[(x+3*y-z, 1, 0)] := by native_decide
example : reducesTo (-(3*x+2*y-4)) #[(4*x+5*y+4, 1, 0)] := by native_decide

/-! ## Quadratics that already fit one row -/

example : reducesTo (x*y) #[(x, y, 0)] := by native_decide
example : reducesTo (x*x) #[(x, x, 0)] := by native_decide
example : reducesTo ((x+1)*(y-2)) #[(x+1, y-2, 0)] := by native_decide
example : reducesTo ((x+y)*(z-1)-(x-z)) #[(x+y, z-1, x-z)] := by native_decide
example : reducesTo ((x-y)*(x+y)) #[(x-y, x+y, 0)] := by native_decide
example : reducesTo ((x+2)*(x+3)-1) #[(x+2, x+3, 1)] := by native_decide
example : reducesTo (x*y+1) #[(x, y, -1)] := by native_decide
example : reducesTo (1-x*y) #[(-x, y, -1)] := by native_decide
example : reducesTo (-(x*y-z)) #[(-x, y, -z)] := by native_decide
example : reducesTo (-(-(x*y-z))) #[(x, y, z)] := by native_decide
example : reducesTo (x*y-(z+1)) #[(x, y, z+1)] := by native_decide
example : reducesTo ((x*y-z)+(x+y)) #[(x, y, z-x-y)] := by native_decide
example : reducesTo ((x+y)-(x*y-z)) #[(-x, y, -z-x-y)] := by native_decide
example : reducesTo (2*(x*y-z)) #[(2*x, y, 2*z)] := by native_decide
example : reducesTo ((x*y-z)*3) #[(3*x, y, 3*z)] := by native_decide
example : reducesTo ((2*x)*(3*y)-z) #[(2*x, 3*y, z)] := by native_decide

-- Nested subtraction changes the signs of both the quadratic and residual parts.
example : reducesTo (x-(y-(x*y-z))) #[(x, y, y+z-x)] := by native_decide
example : reducesTo (x-(y-(z-x*y))) #[(-x, y, y-z-x)] := by native_decide

-- Scaling changes A and C; final linear residuals remain on C.
example : reducesTo (3*(x*y-z)+y) #[(3*x, y, 3*z-y)] := by native_decide
example : reducesTo (2*(z-x*y)-y) #[(-(2*x), y, y-2*z)] := by native_decide
example : reducesTo ((2*x+1)*(3*y-z)-x) #[(2*x+1, 3*y-z, x)] := by native_decide

/-! ## Expressions that become linear or zero -/

example : reducesTo ((x-x)*y-z) #[(-z, 1, 0)] := by native_decide
example : reducesTo ((x+1-x)*y-z) #[(y-z, 1, 0)] := by native_decide
example : reducesTo ((2*x+5*x)*y) #[(0, 1, 0)] := by native_decide
example : reducesTo ((2*x+6*x)*y) #[(x, y, 0)] := by native_decide
example : reducesTo (x*(y-y)) #[(0, 1, 0)] := by native_decide
example : reducesTo (7*(x*y-z)) #[(0, 1, 0)] := by native_decide
example : reducesTo ((x*y-z)*0) #[(0, 1, 0)] := by native_decide
example : reducesTo ((x*y-z)*(x-x)) #[(0, 1, 0)] := by native_decide

-- A zero multiplier cannot hide a reference to a nonexistent original variable.
example : reducesTo (0*t) #[(0, 1, 0)] = false := by native_decide
example : reducesTo (t-t) #[(0, 1, 0)] = false := by native_decide

/-! ## Several assertions share a heap and a compilation state -/

-- No roots produce no rows; repeated roots still produce separate assertions.
example : reducesAllTo #[] #[] := by native_decide
example : reducesAllTo #[0, 0, 1, 1] #[(0, 1, 0), (0, 1, 0), (1, 1, 0), (1, 1, 0)] := by native_decide
example : reducesAllTo #[x, x] #[(x, 1, 0), (x, 1, 0)] := by native_decide
example : reducesAllTo #[x, x - 1] #[(x, 1, 0), (x - 1, 1, 0)] := by native_decide

/-! ## Invalid inputs or inaccurate rows never match -/

-- Compilation failure remains false regardless of the invalid root's position.
example : reducesAllTo #[t, x, y] #[(x, 1, 0), (y, 1, 0)] = false := by native_decide
example : reducesAllTo #[x, t, y] #[(x, 1, 0), (y, 1, 0)] = false := by native_decide
example : reducesAllTo #[x, y, t] #[(x, 1, 0), (y, 1, 0)] = false := by native_decide
-- An invalid variable is reported at once, even with share sites pending.
example : errorOf ((sourceOf #[(x*y)*z, t]).quadraticToR1CS 3 0 3) == some (.invalidVariable 3) := by native_decide

-- Rows are ordered and exact, including defining and repeated assertion rows.
example : reducesAllTo #[x*y - t, t*z, t*x] #[(t, z, 0), (t, x, 0)] (numVars := 4) = false := by native_decide
example : reducesAllTo #[x*y - t, t*z, t*x] #[(x, y, t), (t, z, 0), (x, y, t), (t, x, 0)] (numVars := 4) = false := by native_decide
example : reducesAllTo #[x*y - t, t*z, t*x] #[(t, z, 0), (x, y, t), (t, x, 0)] (numVars := 4) = false := by native_decide
example : reducesAllTo #[0, 0] #[(0, 1, 0)] = false := by native_decide
example : reducesAllTo #[x*y - t, t*z] #[(x, y, -t), (t, z, 0)] (numVars := 4) = false := by native_decide
example : reducesAllTo #[x*y - t, t*z] #[(x, y, 2*t), (t, z, 0)] (numVars := 4) = false := by native_decide
example : reducesAllTo #[x*y - t, t*z] #[(x, y, u), (u, z, 0)] (numVars := 5) = false := by native_decide
-- A rejected system never matches, not even the rows it has once the share is written out.
example : reducesAllTo #[(x*y)*z] #[(x, y, t), (t, z, 0)] (numVars := 4) = false := by native_decide

-- Expected expressions must be linear and refer to wires that actually exist.
example : reducesAllTo #[x, y] #[(x*y, 1, 0), (y, 1, 0)] = false := by native_decide
example : reducesAllTo #[x] #[(x, 1, t)] = false := by native_decide

/-! ## Direct compiler entry points: results and errors -/

def sampleCs := sourceOf #[x*y-z]
def cubicCs := sourceOf #[(x*y)*z]
def linearCs := sourceOf #[x+(y-z)]
def sampleRoot : ExprRef := sampleCs.eq0s[0]!
def cubicRoot : ExprRef := cubicCs.eq0s[0]!
def linearRoot : ExprRef := linearCs.eq0s[0]!

-- The wires are ONE followed by the declared slots, whether or not the rows use them.
example : (quadraticToR1CS sampleCs 3 0 3).toOption.map (·.r1cs.header.nWires) == some 4 := by native_decide
example : (quadraticToR1CS sampleCs 3 0 5).toOption.map (·.r1cs.header.nWires) == some 6 := by native_decide
example : (quadraticToR1CS sampleCs 3 0 3).toOption.map (·.r1cs.header.mConstraints) == some 1 := by native_decide
example : (quadraticToR1CS sampleCs 1 0 3).toOption.map (·.r1cs.header.nPubIn) == some 1 := by native_decide
-- Public inputs first, then private ones; together they must fit in the declared slots.
example : (quadraticToR1CS sampleCs 1 2 3).toOption.map
    (fun c => (c.r1cs.header.nPubIn, c.r1cs.header.nPrvIn)) == some (1, 2) := by native_decide
example : errorOf (quadraticToR1CS sampleCs 2 2 3) == some .invalidInputCount := by native_decide
example : (quadraticToR1CS (sourceOf #[]) 3 0 3).toOption.map (fun c => Array.size c.r1cs.constraints) == some 0 := by native_decide
example : (quadraticToR1CS (sourceOf #[1]) 3 0 3).isOk := by native_decide -- Contradictory still compiles.

-- The cubic's heap is x=e0, y=e1, xy=e2, z=e3, xyz=e4. The structured error names
-- assertion 0, its node e4 (a product), and the quadratic factor e2 to share.
example : cubicRoot == 4 := by native_decide
example : errorOf (quadraticToR1CS cubicCs 3 0 3) == some (.needsShare #[⟨0, 4, .mul, #[2]⟩]) := by native_decide

-- Errors from the full entry point and from `toR1CS`, which returns just the R1CS.
example : errorOf (quadraticToR1CS sampleCs 4 0 3) == some .invalidInputCount := by native_decide
example : errorOf (quadraticToR1CS sampleCs 2 0 2) == some (.invalidVariable 2) := by native_decide
example : errorOf (quadraticToR1CS {sampleCs with eq0s := #[99]} 3 0 3) == some (.invalidRoot 99) := by native_decide
example : errorOf (quadraticToR1CS (sourceOf #[]) 0 0 (2^32-1)) == some .sizeOverflow := by native_decide
example : (toR1CS sampleCs 3 0 3).toOption.map (·.header.nWires) == some 4 := by native_decide
example : errorOf (toR1CS cubicCs 3 0 3) == some (.needsShare #[⟨0, 4, .mul, #[2]⟩]) := by native_decide
example : errorOf (toR1CS sampleCs 4 0 3) == some .invalidInputCount := by native_decide
example : errorOf (toR1CS sampleCs 2 0 2) == some (.invalidVariable 2) := by native_decide
example : errorOf (toR1CS (sourceOf #[]) 0 0 (2^32-1)) == some .sizeOverflow := by native_decide

/-! ## Size checks

A row takes 12 bytes for its three term counts and `4 + fieldSize` bytes per term. -/

example : (checked64 (UInt64.size - 1)).isOk := by native_decide
example : (checked64 UInt64.size).isOk = false := by native_decide

private def byteCountExample : Constraint := ⟨1, 2, 0, #[(1, 1)], #[(1, 1), (2, 1)], #[]⟩

example : constraintBytes 8 #[byteCountExample] = 48 := by native_decide
example : constraintBytes 32 #[byteCountExample, byteCountExample] = 240 := by native_decide

/-! ## Direct normalization: the worker returns a form; the wrapper adds the assertion

These examples use the normalizers themselves, before serialization. Coefficient
pairs are (wire, value); wire 0 is ONE and 1..3 are x,y,z. An operand reported in a
share site stands for a placeholder wire (here 4), as if it were shared, so lowering can
go on and find later sites; `quadraticToR1CS` then throws instead of emitting such rows.
-/

private def rowCoefficients (q : NormalQuadratic 7) := (q.A, q.B, q.C)

-- x+(y-z) is linear and xy-z is quadratic; neither needs a share.
example : ((normalQuadratic₀ linearCs.σ 3 0 linearRoot).run {}).toOption.map (fun (r, s) => (r.isLeft, s.rows.size)) == some (true, 0) := by native_decide
example : ((normalQuadratic₀ sampleCs.σ 3 0 sampleRoot).run {}).toOption.map (fun (r, s) => (r.isRight, s.rows.size)) == some (true, 0) := by native_decide
example : ((normalQuadratic₀ sampleCs.σ 3 0 sampleRoot).run {}).toOption.map (fun (r, _) => r.elim (fun _ => none) (some ∘ rowCoefficients)) == some (some ([(1,1)], [(2,1)], [(3,1)])) := by native_decide

-- Reducing xyz records one site and emits no row; the wrapper's row uses placeholder wire 4 for xy.
example : ((normalQuadratic₀ cubicCs.σ 3 0 cubicRoot).run {}).toOption.map (fun (r, s) => (r.isRight, s.rows.size, s.sites.size)) == some (true, 0, 1) := by native_decide
example : ((normalQuadratic 3 sampleCs.σ 0 sampleRoot).run {}).toOption.map (fun (_, s) => s.rows.map rowCoefficients) == some #[([(1,1)], [(2,1)], [(3,1)])] := by native_decide
example : ((normalQuadratic 3 cubicCs.σ 0 cubicRoot).run {}).toOption.map (fun (_, s) => s.rows.map rowCoefficients) == some #[([(4,1)], [(3,1)], [])] := by native_decide
example : errorOf ((normalQuadratic 3 sampleCs.σ 0 99).run {}) == some (.invalidRoot 99) := by native_decide
example : errorOf ((normalQuadratic₀ sampleCs.σ 2 0 sampleRoot).run {}) == some (.invalidVariable 2) := by native_decide

/-! ## Witness functions tested without calling the compiler -/

-- Hand-built artifact: xy=z. The R1CS witness is ONE followed by the trace, unchanged.
private def witnessFixture : Compilation 7 :=
  let rows : Constraints := #[⟨1, 1, 1, #[(1, 1)], #[(2, 1)], #[(3, 1)]⟩]
  let r1cs : R1CSv1 := ⟨⟨8, 7, 4, 0, 3, 0, 4, 1⟩, rows, #[0,1,2,3], (), ()⟩
  ⟨r1cs, 3⟩

example : (witnessFixture.toWtns #[2,3,6]).toOption.map (·.elements) == some #[1,2,3,6] := by native_decide
example : (witnessFixture.toWtns #[6,6,1]).toOption.map (·.elements) == some #[1,6,6,1] := by native_decide -- 36 mod 7 = 1.
example : (witnessFixture.toWtns #[2,3,6]).toOption.map (·.nVars) == some 4 := by native_decide
example : (witnessFixture.toWtns #[2,3,6]).toOption.map (·.n8) == some 8 := by native_decide
example : (witnessFixture.toWtns #[2,3,6]).toOption.map (·.prime) == some 7 := by native_decide
example : errorOf (witnessFixture.toWtns #[2,3]) == some .witnessLength := by native_decide
example : errorOf (witnessFixture.toWtns #[2,3,6,0]) == some .witnessLength := by native_decide

-- The witness API does not check satisfaction: 2*3 ≠ 4.
example : (witnessFixture.toWtns #[2,3,4]).toOption.map (·.elements) == some #[1,2,3,4] := by native_decide

end Clap.Test.R1CS
