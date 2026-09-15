import Clap.eDSLState.Circuit
import Clap.eDSLState.Varstore

import Clap.eDSLState.ConstraintSystem.eq0
import Clap.eDSLState.ConstraintSystem.fpMul
import Clap.eDSLState.ConstraintSystem.isZero
import Clap.eDSLState.ConstraintSystem.num2bits
import Clap.eDSLState.ConstraintSystem.share

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
    1 + k * (w + 3)

def offsetSince (threshold idx offset : ℕ) : ℕ :=
  if idx < threshold then idx else idx + offset

/--
Not to be confused with Colonel Allocs.
-/
def privateAllocs (gate : Gate) : ℕ :=
  match gate with
  | .eq0 _ => 0
  | .share _ => 0
  | .isZero _ => 1
  | .num2bits .. => 0
  | .fpmul w k .. =>
    -- `rangeCheckInputs #[] numAlloc width a b p'`
    3 * k * w +
    -- `polyMult constraints numAlloc a b`
    k +
    -- `allocRangeChecked constraints numAlloc k width` (for `q`)
    k * w + k +
    -- PUBLIC: `allocRangeChecked constraints numAlloc k width` (for `r`) (I think; TODO)
    -- k * w + k +
    0 +
    -- `allocUnchecked numAlloc (2 * k - 1)`
    k +
    -- `inner constraints ab t p' q r`
    0 +
    -- `check_carry_zero constraints numAlloc width t`
    (if k == 0 then 0 else k - 1) +
    -- `check_lt constraints numAlloc width r p'`
    k * (w + 2)
    -- TODO replace with subtraction of circuit step numAlloc from cs numalloc

def offsetIdx (circuit : Circuit) : ℕ → ℕ :=
  (·.1) <| circuit.foldr (init := (id, circuit.numAllocStep))
    fun gate (f, threshold) ↦
      let privateAllocs := privateAllocs gate
      let publicAllocs := gate.numAllocStep
      /-
        [public₁, public₂]
                         ^ threshold
        ^ threshold - publicAllocs
        [priv₁, priv₂, public₁, public₂]
      -/
      let nextThreshold := threshold - publicAllocs
      -- dbg_trace s!"t: {threshold}\npriv: {privateAllocs}\npublic: {publicAllocs}\nnextT: {nextThreshold}"
      let yourFace := fun idx ↦ offsetSince nextThreshold (f idx) privateAllocs
      -- dbg_trace s!"{List.range 50 |>.map yourFace}"
      (yourFace, nextThreshold)

-- def offsetIdx' (circuit : Circuit) (idx : ℕ) : ℕ :=
--   let allPrivateAllocs := (circuit.map privateAllocs).sum
--   let allAllocs := circuit.numAllocStep + allPrivateAllocs
--   let idxs := (circuit.mapIdx (λ idx gate => (
--     let preceding := circuit.take idx
--     let start := Circuit.numAllocStep preceding + (preceding.map privateAllocs).sum
--     let privates := (List.range' start (privateAllocs gate)).map (λ x => (false, x))
--     let publics := (List.range' (start + privateAllocs gate) gate.numAllocStep).map (λ x => (true, x))
--     privates ++ publics
--   ))).toList.flatten
--   dbg_trace s!"{idxs}"
--   if idx > circuit.numAllocStep
--   then idx + allPrivateAllocs
--   else (idxs.filter Prod.fst)[idx]!.2

def offsetHashConsState {p : ℕ}
  (σ : HashConsSt p) (circuit : Circuit)
: HashConsSt p :=
  let offsets := offsetIdx circuit
  let exprs := σ.exprs.map (λ cacheExpr => match cacheExpr with
    | .c x=> .c x
    | .v x => .v (offsets x)
    | .binary_op lhs rhs op => .binary_op lhs rhs op
  )
  let wellFormed := by
    intro i h_i
    obtain ⟨_, h_wellFormed⟩ := σ
    specialize h_wellFormed i (by grind)
    grind
  ⟨exprs, wellFormed⟩


def Circuit.toCs {p : ℕ} (circuit : Circuit) (σ : HashConsSt p) (numInputs : ℕ)
:
  ConstraintSystem p
:=
  let σMapped := offsetHashConsState σ circuit
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
