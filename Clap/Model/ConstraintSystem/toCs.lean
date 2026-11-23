import Clap.Model.Circuit
import Clap.Model.Varstore

import Clap.Model.ConstraintSystem.eq0
import Clap.Model.ConstraintSystem.fpMul
import Clap.Model.ConstraintSystem.isZero
import Clap.Model.ConstraintSystem.num2bits
import Clap.Model.ConstraintSystem.share

namespace Clap

open HashConsM

structure ConstraintSystem (p : ℕ) where
  eq0s : Array ExprRef
  σ : HashConsSt p

namespace ConstraintSystem

open HashConsM

variable {p : ℕ} (cs: ConstraintSystem p)

def runSpec (trace : Array (ZMod p)) : Bool :=
  cs.eq0s.all (λ expr => [.ofArray (trace.zipIdx.map Prod.swap), cs.σ|expr] == .some 0)

-- TODO prove equivalent to runSpec
-- TODO make evalWithArrayCache to avoid the conversion and prove equivalent to evalWithCache
def run (trace : Array (ZMod p)) : Bool :=
  let max := cs.eq0s.max?
  match max with
  | .none => true
  | .some max =>
    let cache := Expr.evalWithCache (.ofArray (trace.zipIdx.map Prod.swap)) #[] ⦃max, cs.σ⦄
    cs.eq0s.all (λ expr => cache[expr]? == .some (0 : ZMod p))

def num_constraints : Gate → ℕ
  | .eq0 _ => 1
  | .share _ => 1
  | .isZero _ => 2
  | .num2bits w _ => w + 1
  | .fpmul w k .. =>
    -- `rangeCheckInputs #[] numAlloc width a b p'`
    3 * k * w + 3 * k +
    -- `polyMult constraints numAlloc a b`
    2 * k - 1 +
    -- `allocRangeChecked constraints numAlloc k width` (for `q`)
    k * w + k +
    -- `allocRangeChecked constraints numAlloc k width` (for `r`)
    k * w + k +
    -- `allocUnchecked numAlloc (2 * k - 1)`
    0 +
    -- `inner constraints ab t p' q r`
    2 * k - 1 +
    -- `check_carry_zero constraints numAlloc width t`
    (if k == 0 then 0 else 1) +
    -- `check_lt constraints numAlloc width r p'`
    1 + k * (w + 4)

/-- Number of trace slots `Circuit.toCs` gives `gate` -/
def gateSlots : Gate → ℕ
  | .eq0 _ => eq0.numAllocStep
  | .share _ => share.numAllocStep
  | .isZero _ => isZero.numAllocStep
  | .num2bits w _ => num2bits.numAllocStep w
  | .fpmul w k .. => fpMul.numAllocStep w k

/-- Where the gate's outputs sit in its block of `gateSlots gate` trace slots.
* `isZero` 1 (after the inverse)
* `fpmul` allocates the range-check bits of `a`, `b` and `p'` (`k` num2bits of width `w` each),
  then `ab` (`2k - 1`), then `q` and its bits, then the output `r`, then `r`'s bits, `t`, the
  carries and `check_lt`, whose `k` shared flags come last.
* Every other gate's block is its outputs. -/
def outputOffset : Gate → ℕ
  | .isZero _ => 1
  | .fpmul w k .. => 3 * k * num2bits.numAllocStep w + (2 * k - 1) + k * (1 + num2bits.numAllocStep w)
  | _ => 0

/-- `table` with `start, start + 1, …, start + n - 1` pushed. -/
def pushRange (table : Array ℕ) (start : ℕ) : ℕ → Array ℕ
  | 0 => table
  | n + 1 => pushRange (table.push start) (start + 1) n

def slotTable (circuit : Circuit) : Array ℕ × ℕ := go 0 #[] 0
where
  go (i : ℕ) (table : Array ℕ) (base : ℕ) : Array ℕ × ℕ :=
    if h : i < circuit.size then
      let gate := circuit[i]
      go (i + 1) (pushRange table (base + outputOffset gate) gate.numAllocStep)
        (base + gateSlots gate)
    else (table, base)
  termination_by circuit.size - i

/-- The trace slot (past the inputs) of ClapM variable `idx` (past the inputs), from a
`slotTable`. A variable past the gates' outputs keeps its distance from the end of the trace. -/
def slotOf (slots : Array ℕ × ℕ) (idx : ℕ) : ℕ :=
  slots.1[idx]?.getD (idx - slots.1.size + slots.2)

/-- The trace slot (past the inputs) of ClapM variable `idx` (past the inputs). -/
def offsetIdx (circuit : Circuit) : ℕ → ℕ :=
  slotOf (slotTable circuit)

/-- `σ` with each variable `.v x` past the inputs (`numInputs ≤ x`) moved to slot
`numInputs + offsets (x - numInputs)`. -/
def remapVars {p : ℕ} (offsets : ℕ → ℕ) (numInputs : ℕ) (σ : HashConsSt p) : HashConsSt p :=
  let exprs := σ.exprs.map (λ cacheExpr => match cacheExpr with
    | .c x=> .c x
    | .v x => .v (if x < numInputs then x else numInputs + offsets (x - numInputs))
    | .binary_op lhs rhs op => .binary_op lhs rhs op
  )
  let wellFormed := by
    intro i h_i
    obtain ⟨_, h_wellFormed, _, _⟩ := σ
    specialize h_wellFormed i (by grind)
    grind
  HashConsSt.ofExprs exprs wellFormed

/-- `σ` with each ClapM variable renamed to its trace slot. the inputs (`x < numPublicInputs`)
stay, the gates' outputs go through `slotTable`

The table is bound before the call: passed as `offsetIdx circuit`, the compiler eta-expands
`slotOf (slotTable circuit)` into a lambda that rebuilds the table for every heap node. -/
def offsetHashConsState {p : ℕ}
  (numPublicInputs : ℕ)
  (σ : HashConsSt p) (circuit : Circuit)
: HashConsSt p :=
  let slots := slotTable circuit
  remapVars (slotOf slots) numPublicInputs σ

def _root_.Clap.Circuit.toCs {p : ℕ} (circuit : Circuit) (σ : HashConsSt p) (numInputs : ℕ)
:
  ConstraintSystem p
:=
  let σMapped := offsetHashConsState numInputs σ circuit
  let ((eq0s, _numAlloc), σPost) :=
    (circuit.foldlM (m := HashConsM p) (λ (eq0s, numAlloc) gate => do
      match gate with
      | .eq0 expr => eq0 eq0s numAlloc expr
      | .share expr => return (←share eq0s numAlloc expr).2
      | .isZero expr => return (←isZero eq0s numAlloc expr).2
      | .num2bits width expr => return (←num2bits eq0s numAlloc width expr).2
      | .fpmul w k a b p' => return (←fpMul eq0s numAlloc w k a b p').2
    ) (Array.emptyWithCapacity (circuit.map ConstraintSystem.num_constraints).sum , numInputs)).run σMapped
  ⟨eq0s, σPost⟩

end Clap.ConstraintSystem
