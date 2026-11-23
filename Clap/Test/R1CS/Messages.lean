import Clap.Compiler.Compile
import Clap.Test.R1CS.Lowering

/-!
# Share sites and error messages

A lowering that needs a `share` fails with `needsShare`, naming every node and the operands to
share (rendered by `renderExpr`, Clap/Compiler/Compile.lean), and `CompileError.render` turns the
error into a message.
-/

namespace Clap.Test.R1CS

open HashConsM
open Clap.ConstraintSystem

/-- The share sites reported for `inputs`: assertion index, offending node, and the
operands to share. Expressions are rendered over v0,v1,v2,... (x,y,z,...).
`none` unless compilation fails with `needsShare`. -/
private def sharesOf (inputs : Array TestExpr) : Option (Array (Nat × String × Array String)) :=
  let cs := sourceOf inputs
  match cs.quadraticToR1CS 3 0 3 with
  | .error (.needsShare sites) =>
    some (sites.map fun s => (s.assertion, renderExpr cs.σ s.node, s.operands.map (renderExpr cs.σ)))
  | _ => none

/-- One assertion is rejected, with exactly these `(node, operands to share)`. -/
private def needsShare (input : TestExpr) (expected : Array (String × Array String)) : Bool :=
  sharesOf #[input] == some (expected.map (0, ·))

/-- The rendered compile error for `inputs`, or "ok". -/
private def messageOf (inputs : Array TestExpr) : String :=
  let cs := sourceOf inputs
  match cs.quadraticToR1CS 3 0 3 with
  | .error e => e.render cs.σ
  | .ok _ => "ok"

/-! ## Products of a quadratic need an explicit `share`

The compiler adds no witness variables. When a node does not fit one row, compilation
fails with `needsShare`, naming the node and the operands to share. Writing each shared
value as a source variable t (and u) gives back one row per assertion.
-/

example : needsShare ((x * y) * z) #[("v0 * v1 * v2", #["v0 * v1"])] := by native_decide
example : reducesAllTo #[x * y - t, t * z] #[(x, y, t), (t, z, 0)] (numVars := 4) := by native_decide

-- For a sum of two products, sharing either is enough; the right one is suggested first.
example : needsShare (x*y + y*z) #[("v0 * v1 + v1 * v2", #["v1 * v2", "v0 * v1"])] := by native_decide
example : reducesAllTo #[y * z - t, x * y + t] #[(y, z, t), (x, y, -t)] (numVars := 4) := by native_decide

example : needsShare ((x * y - z) * x) #[("(v0 * v1 - v2) * v0", #["v0 * v1 - v2"])] := by native_decide
example : reducesAllTo #[x * y - z - t, t * x] #[(x, y, z + t), (t, x, 0)] (numVars := 4) := by native_decide

-- Both quadratic factors must be shared: t=xy-z and u=yz-x.
example : needsShare ((x*y-z)*(y*z-x))
    #[("(v0 * v1 - v2) * (v1 * v2 - v0)", #["v0 * v1 - v2", "v1 * v2 - v0"])] := by native_decide
example : reducesAllTo #[x*y - z - t, y*z - x - u, t*u]
    #[(x, y, z+t), (y, z, x+u), (t, u, 0)] (numVars := 5) := by native_decide

-- Product-plus-residual factors keep their linear terms in their defining rows.
example : needsShare ((x*y+z)*(y*z+x)-1)
    #[("(v0 * v1 + v2) * (v1 * v2 + v0)", #["v0 * v1 + v2", "v1 * v2 + v0"])] := by native_decide
example : reducesAllTo #[x*y + z - t, y*z + x - u, t*u - 1]
    #[(x, y, t-z), (y, z, u-x), (t, u, 1)] (numVars := 5) := by native_decide

/-! ## Expressions that become linear or zero -/

-- Children are lowered before the zero shortcut: every reachable node must fit one row.
example : needsShare (0*((x*y)*z)) #[("v0 * v1 * v2", #["v0 * v1"])] := by native_decide
example : needsShare (((x*y)*z)*0) #[("v0 * v1 * v2", #["v0 * v1"])] := by native_decide
example : needsShare (0*((x*y-z)*(y*z-x)))
    #[("(v0 * v1 - v2) * (v1 * v2 - v0)", #["v0 * v1 - v2", "v1 * v2 - v0"])] := by native_decide
-- Hash-consing makes both sides one node, so there is one operand to share.
example : needsShare ((x*y)-(x*y)) #[("v0 * v1 - v0 * v1", #["v0 * v1"])] := by native_decide

/-! ## Every share site is reported in one error

Lowering continues as if each reported operand were shared, so one compilation lists
every site, in traversal order (left to right, children first). Each operand is
reported once, at its first use.
-/

-- A chain of products: each intermediate product is a site.
example : sharesOf #[((x*y)*z)*x - y] == some #[
    (0, "v0 * v1 * v2", #["v0 * v1"]),
    (0, "v0 * v1 * v2 * v0", #["v0 * v1 * v2"])] := by native_decide
example : reducesAllTo #[x*y - t, t*z - u, u*x - y] #[(x, y, t), (t, z, u), (u, x, y)] (numVars := 5) := by native_decide

example : sharesOf #[((x*y)*(y*z))*x - 1] == some #[
    (0, "v0 * v1 * (v1 * v2)", #["v0 * v1", "v1 * v2"]),
    (0, "v0 * v1 * (v1 * v2) * v0", #["v0 * v1 * (v1 * v2)"])] := by native_decide

example : sharesOf #[((x*y-z)*x-y)*z-1] == some #[
    (0, "(v0 * v1 - v2) * v0", #["v0 * v1 - v2"]),
    (0, "((v0 * v1 - v2) * v0 - v1) * v2", #["(v0 * v1 - v2) * v0 - v1"])] := by native_decide
example : reducesAllTo #[x*y - z - t, t*x - y - u, u*z - 1] #[(x, y, z+t), (t, x, y+u), (u, z, 1)] (numVars := 5) := by native_decide

-- A difference of products and then its product: one sum site and one product site.
example : sharesOf #[(x*y-y*z)*(x+z)-1] == some #[
    (0, "v0 * v1 - v1 * v2", #["v1 * v2", "v0 * v1"]),
    (0, "(v0 * v1 - v1 * v2) * (v0 + v2)", #["v0 * v1 - v1 * v2"])] := by native_decide
example : reducesAllTo #[y*z - t, x*y - t - u, u*(x+z) - 1] #[(y, z, t), (x, y, t+u), (u, x+z, 1)] (numVars := 5) := by native_decide

-- The same product used twice is one operand to share.
example : needsShare ((x*y)*(x*y)-z) #[("v0 * v1 * (v0 * v1)", #["v0 * v1"])] := by native_decide
example : reducesAllTo #[x*y - t, t*t - z] #[(x, y, t), (t, t, z)] (numVars := 4) := by native_decide

-- xy is reported at its first use only; the sum of the two products is a second site.
example : sharesOf #[((x*y)*z)+((x*y)*x)-y] == some #[
    (0, "v0 * v1 * v2", #["v0 * v1"]),
    (0, "v0 * v1 * v2 + v0 * v1 * v0", #["v0 * v1 * v0", "v0 * v1 * v2"])] := by native_decide
example : reducesAllTo #[x*y - t, t*x - u, t*z + u - y] #[(x, y, t), (t, x, u), (t, z, y-u)] (numVars := 5) := by native_decide

/-! ## Several assertions share a heap and a compilation state -/

-- A site records the assertion where its node was first reached. An operand already
-- reported for one assertion is not reported again for another.
example : sharesOf #[(x*y)*z, (x*y)*x] == some #[(0, "v0 * v1 * v2", #["v0 * v1"])] := by native_decide
example : sharesOf #[x*y, (x*y)*z] == some #[(1, "v0 * v1 * v2", #["v0 * v1"])] := by native_decide
example : reducesAllTo #[x*y - t, t*z, t*x] #[(x, y, t), (t, z, 0), (t, x, 0)] (numVars := 4) := by native_decide
-- Equivalent expressions with different syntax are distinct heap nodes, hence distinct sites.
example : sharesOf #[(x*y)*z, (y*x)*z] == some #[
    (0, "v0 * v1 * v2", #["v0 * v1"]),
    (1, "v1 * v0 * v2", #["v1 * v0"])] := by native_decide

/-! ## Error messages

`CompileError.render` (used by `compileExplained` and `compile`) prints each
site as the offending node and the operands to share. `e{ref}` is the heap reference
(the same ref a ClapM gadget holds) and `v{i}` is trace slot i.
-/

example : messageOf #[(x*y)*z] == lines [
    "1 node is not rank-1 and needs auxiliary witness variables. Share the listed operands:",
    "• assertion 0: product with a quadratic factor",
    "    e4 := v0 * v1 * v2",
    "  share e2 := v0 * v1"] := by native_decide

-- Sum: sharing either operand fixes it.
example : messageOf #[x*y + y*z] == lines [
    "1 node is not rank-1 and needs auxiliary witness variables. Share the listed operands:",
    "• assertion 0: sum of two quadratics",
    "    e5 := v0 * v1 + v1 * v2",
    "  share e4 := v1 * v2",
    "  or    e2 := v0 * v1"] := by native_decide

-- Product of two quadratics: both factors must be shared.
example : messageOf #[(x*y-z)*(y*z-x)] == lines [
    "1 node is not rank-1 and needs auxiliary witness variables. Share the listed operands:",
    "• assertion 0: product of two quadratic factors",
    "    e7 := (v0 * v1 - v2) * (v1 * v2 - v0)",
    "  share e4 := v0 * v1 - v2",
    "  and   e6 := v1 * v2 - v0"] := by native_decide

-- Every site is listed.
example : messageOf #[(x*y)*z, (y*z)*x, (z*x)*y] == lines [
    "3 nodes are not rank-1 and need auxiliary witness variables. Share the listed operands:",
    "• assertion 0: product with a quadratic factor",
    "    e4 := v0 * v1 * v2",
    "  share e2 := v0 * v1",
    "• assertion 1: product with a quadratic factor",
    "    e6 := v1 * v2 * v0",
    "  share e5 := v1 * v2",
    "• assertion 2: product with a quadratic factor",
    "    e8 := v2 * v0 * v1",
    "  share e7 := v2 * v0"] := by native_decide

-- Other errors get a one-line message; systems that compile give no message.
example : messageOf #[t] == "variable v3 is not one of the declared witness slots" := by native_decide
example : messageOf #[x*y - z] == "ok" := by native_decide
example : (compileExplained sampleCs 3 0 3).isOk := by native_decide
example : (compileExplained cubicCs 3 0 3).toOption.isNone := by native_decide

end Clap.Test.R1CS
