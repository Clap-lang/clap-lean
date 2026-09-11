import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.ConstraintSystem.isZero
import Clap.eDSLState.ConstraintSystem.num2bits

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

--k*width+k constraints, k*width allocations
def rangeCheckVec {p k : ℕ} (constraints : Array (BoundRef p)) (numAlloc width : ℕ) (vec : Vector (BoundRef p) k) : HashConsM p (Array (BoundRef p) × ℕ) := do
  vec.foldlM (b := (constraints, numAlloc)) fun (constraints, numAlloc) elem ↦ do
    let (_bits, constraints, numAlloc) ← num2bits constraints numAlloc width elem
    return (constraints, numAlloc)

def evalPoly {p k : ℕ} (coeffs : Vector (BoundRef p) k) (x : ZMod p) : HashConsM p (BoundRef p) := do
  (List.finRange k).foldrM
    (fun ind acc => do
      let term ← coeffs[ind] * (←mkConstant (x ^ ind.val))
      acc + term
    ) (←mkConstant 0)

-- return size 2*k - 1
def assertPolyEqProd {p k : ℕ}
    (a : Vector (BoundRef p) k)
    (b : Vector (BoundRef p) k)
    (c : Vector (BoundRef p) (2 * k - 1)) : HashConsM p (Array (BoundRef p)) :=
  (Array.range (2 * k - 1)).mapM
    fun (k : ℕ) ↦ do
      let mul ← (←evalPoly a k) * (←evalPoly b k)
      mul - (←evalPoly c k)

-- 3*k*width + 3*k constraints, 3*k*width allocations
def rangeCheckInputs
  {p k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (a b p' : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  let (constraints, numAlloc) ← rangeCheckVec constraints numAlloc width a
  let (constraints, numAlloc) ← rangeCheckVec constraints numAlloc width b
  let (constraints, numAlloc) ← rangeCheckVec constraints numAlloc width p'
  return (constraints, numAlloc)

-- k allocations
def allocUnchecked
  {p : ℕ}
  (numAlloc : ℕ)
  (k : ℕ)
: HashConsM p (Vector (BoundRef p) k × ℕ) := do
  let vec ← Vector.ofFnM fun i : Fin k ↦ mkVar (numAlloc + i)
  return (vec, numAlloc + k)

--k*width+k constraints, k*width+k allocations
def allocRangeChecked
  {p : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (k : ℕ)
  (width : ℕ)
: HashConsM p (Vector (BoundRef p) k × (Array (BoundRef p) × ℕ)) := do
  let (vec, numAlloc) ← allocUnchecked numAlloc k
  let (constraints, numAlloc) ← rangeCheckVec constraints numAlloc width vec
  return (vec, (constraints, numAlloc))

-- 2*k-1 constraints, k allocations
def polyMult
  {p k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (a b : Vector (BoundRef p) k)
: HashConsM p (Vector (BoundRef p) (2*k-1) × (Array (BoundRef p) × ℕ)) := do
  let (ab, numAlloc) ← allocUnchecked numAlloc (2*k-1)
  let prodConstraints ← assertPolyEqProd a b ab
  return (ab, (constraints ++ prodConstraints, numAlloc))

-- if k = 0 then 0 allocations, 0 constraints
-- else k-1 allocations
--      0 constraints
/-
        + (k-1) * 1 + num2bits.num_constraints (width + Nat.clog 2 k + 2)
        + 1
-/
def check_carry_zero
  {p : ℕ}
  {k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (t : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  if _ : k = 0 then return (constraints, numAlloc)
  else
    let (carry, numAlloc) ← allocUnchecked numAlloc (k - 1)
    let (constraints, numAlloc) ← (List.finRange (k - 1)).foldrM (λ (i : Fin (k - 1)) (constraints, numAlloc) => do
      let e ← if _ : i.val = 0
        then pure t[i]
        else t[i] + carry[(⟨i - 1, by omega⟩ : Fin (k - 1))]
      let constraints := constraints.push (←e - (←(←mkConstant (2^width)) * carry[i]))
      let (_bits, constraints, numAlloc) ← num2bits
          (width := width + Nat.clog 2 k + 2)
          (numAlloc := numAlloc) (constraints := constraints)
          (expr := ← carry[i] + (←mkConstant (k * 2 ^ (width + 1))))
      return (constraints, numAlloc)
    ) (constraints, numAlloc)
    let overflow ← t[(⟨k - 1, by omega⟩ : Fin k)] + (
        ←if _ : k = 1 then mkConstant 0
        else pure carry[(⟨k - 2, by omega⟩ : Fin (k - 1))]
    )
    return (constraints.push overflow, numAlloc)

def mkOr {p} (a b : BoundRef p) : HashConsM p (BoundRef p) := do
  (←a + b) - (←a*b)

def mkNot {p} (a : BoundRef p) : HashConsM p (BoundRef p) := do
  (←mkConstant 1) - a

/-
k = 0 : 1 constraints, 0 allocations
k = n+1 :
  num2bits : width+1 constraints, width allocations
  isZero : 2 constraints, 2 allocations

constraints : 1 + k*(width + 3)
allocations : k*(width + 2)
-/
def check_lt_impl
  {p : ℕ}
  {k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (isLt : (BoundRef p))
  (a b : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ):= do
  match _ : k with
  | .zero => return (constraints.push (←isLt - (←mkConstant 1)), numAlloc)
  | .succ k =>
    let (_bits, constraints, numAlloc) ← num2bits
      (constraints := constraints)
      (numAlloc := numAlloc)
      (width := width)
      (expr := ←
        (←(←mkConstant 1) - isLt) *
        (←
          (←a[Fin.last k] - b[Fin.last k]) +
          (←mkConstant ((2 ^ width : ZMod p) - 1))
        )
      )

    let (isz, constraints, numAlloc) ← isZero constraints numAlloc (←a[Fin.last k] - b[Fin.last k])

    let isLt' ← mkOr isLt (←mkNot isz)

    let a' := Vector.ofFn (fun (i : Fin k) ↦ a[i.castSucc])
    let b' := Vector.ofFn (fun (i : Fin k) ↦ b[i.castSucc])

    check_lt_impl constraints numAlloc width isLt' a' b'

def check_lt
  {p : ℕ}
  {k}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (a b : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  check_lt_impl constraints numAlloc width (←mkConstant 0) a b

def inner
  {p}
  {k}
  (constraints : Array (BoundRef p))
  (ab t : Vector (BoundRef p) (2*k-1))
  (p' q r : Vector (BoundRef p) k)
:
  HashConsM p (Array (BoundRef p))
:= do
  (List.range (2*k - 1)).foldrM (λ (x : ℕ) constraints ↦ do
    let pq_plus_r ← (←(←evalPoly p' x) * (←evalPoly q x)) + (←evalPoly r x)
    let ab_sub ← (←evalPoly ab x) - pq_plus_r
    let res ← (←evalPoly t x) - ab_sub
    return constraints.push res
  ) (constraints)

def fpMul_impl {p : ℕ}
  (numAlloc : ℕ)
  (width k : ℕ)
  (a b p' : Vector (BoundRef p) k)
:
  HashConsM p (Vector (BoundRef p) k × Array (BoundRef p) × ℕ)
:= do
  let (constraints, numAlloc) ← rangeCheckInputs #[] numAlloc width a b p'

  let (ab, (constraints, numAlloc)) ← polyMult constraints numAlloc a b

  let (q, (constraints, numAlloc)) ← allocRangeChecked constraints numAlloc k width
  let (r, (constraints, numAlloc)) ← allocRangeChecked constraints numAlloc k width
  let (t, numAlloc) ← allocUnchecked numAlloc (2*k - 1)

  let constraints ← inner constraints ab t p' q r

  let (constraints, numAlloc) ← check_carry_zero constraints numAlloc width t

  let (constraints, numAlloc) ← check_lt constraints numAlloc width r p'

  return (r, constraints, numAlloc)

def fpMul {p : ℕ}
  (constraints : Array ExprRef) (numAlloc : ℕ)
  (width k : ℕ)
  (a b p' : Vector (BoundRef p) k)
:
  HashConsM p (Vector (BoundRef p) k × Array (BoundRef p) × ℕ)
:= do
  let (result, fpmul_constraints, numAlloc) ← fpMul_impl
    (numAlloc := numAlloc)
    (width := width)
    (k := k)
    a b p'
  return (result, constraints ++ fpmul_constraints, numAlloc)


namespace fpMul

def num_constraints (width k: ℕ) : ℕ :=
  if k = 0 then 1
  else
    -- TODO fix priority on deref
    (Nat.mul 2 (k-1)) * (Nat.clog 2 (2 * k - 1) : ℕ) +
    (8*k-2) * width +
    20*k
    - 8


def numAllocStep (width k : ℕ) : ℕ := if k = 0 then 0
else
  (k * 6) * num2bits.numAllocStep width +
  (8 * k - 4) +
  (2 * k - 2) * num2bits.numAllocStep (width + Nat.clog 2 (2 * k - 1) + 2) +
  k * isZero.numAllocStep

@[simp, grind =]
lemma allocUnchecked_numAllocStep
  {p}
  {numAlloc}
  {k}
  {σ : HashConsSt p}
:
  ((allocUnchecked numAlloc k).getResult σ).2 =
  numAlloc + k
:= by
  simp [allocUnchecked]

@[simp, grind =]
lemma check_carry_zero_num_constraints
  {p : ℕ}
  {k}
  {constraints : Array (BoundRef p)} {numAlloc : ℕ}
  {width : ℕ}
  {a : Vector (BoundRef p) k}
  {σ}
:
  ((check_carry_zero constraints numAlloc width a).getResult σ).1.size =
  constraints.size + if k = 0 then 0 else
  (k-1) * (1 + num2bits.num_constraints (width + Nat.clog 2 k + 2)) + 1
:= by
  simp [check_carry_zero]
  obtain _ | k := k
  . simp
  . obtain _ | k := k
    . simp
    . simp
      set f := λ i x => _

      have h_f (x) (constraints) (numAlloc) (σ) :
        ((f x (constraints, numAlloc)).getResult σ).1.size =
        constraints.size + 1 + num2bits.num_constraints (width + Nat.clog 2 (k + 1 + 1) + 2)
      := by
        subst f
        simp
        split <;> simp

      generalize (allocUnchecked numAlloc (k + 1)).getHashConsState σ = σ
      generalize numAlloc + (k + 1) = numAlloc
      have : (List.finRange (k + 1)).length = k + 1 := by grind
      set l := List.finRange (k + 1)
      clear_value l
      clear_value f
      set x := width + Nat.clog 2 (k + 1 + 1) + 2
      clear_value x
      have :
        (k + 1) * (1 + num2bits.num_constraints x) =
        l.length * (1 + num2bits.num_constraints x)
      := by grind
      rewrite [this]
      clear this
      obtain _ | ⟨hd, tl⟩ := l
      . exfalso; grind
      . clear this
        induction' tl with head tail h_tail
        . simp [h_f, add_assoc]
        . simp [h_f]
          simp [h_f] at h_tail
          rewrite [h_tail]
          grind

@[simp, grind =]
lemma check_carry_zero_numAlloc
  {p : ℕ}
  {k}
  {constraints : Array (BoundRef p)} {numAlloc : ℕ}
  {width : ℕ}
  {a : Vector (BoundRef p) k}
  {σ}
:
  ((check_carry_zero constraints numAlloc width a).getResult σ).2 =
  numAlloc + if k = 0
  then 0
  else ((k-1) * (1 + num2bits.numAllocStep (width + Nat.clog 2 k + 2)))
:= by
  simp [check_carry_zero]
  obtain _ | k := k
  . simp
  . obtain _ | k := k
    . simp
    . simp
      set f := λ i x => _

      have h_f (x) (constraints) (numAlloc) (σ) :
        ((f x (constraints, numAlloc)).getResult σ).2 =
        numAlloc + num2bits.numAllocStep (width + Nat.clog 2 (k + 1 + 1) + 2)
      := by
        subst f
        simp
        split <;> simp

      generalize (allocUnchecked numAlloc (k + 1)).getHashConsState σ = σ
      have : (List.finRange (k + 1)).length = k + 1 := by grind
      set l := List.finRange (k + 1)
      clear_value l
      clear_value f
      set x := width + Nat.clog 2 (k + 1 + 1) + 2
      clear_value x
      have :
        (k + 1) * (1 + num2bits.numAllocStep x) =
        l.length * (1 + num2bits.numAllocStep x)
      := by grind

      rewrite [this]; clear this
      rewrite [show numAlloc + (k + 1) = numAlloc + l.length by grind]
      clear this
      generalize eq:numAlloc + l.length = numAlloc'
      rewrite [mul_add, mul_one, ←add_assoc, eq]
      clear eq
      induction' l with head tail ih generalizing numAlloc'
      . grind
      . simp [h_f]
        rewrite [ih]
        grind

@[simp, grind =]
lemma check_lt_num_constraints
  {p : ℕ}
  {k}
  {constraints : Array (BoundRef p)} {numAlloc : ℕ}
  {width : ℕ}
  {a b : Vector (BoundRef p) k}
  {σ}
:
  ((check_lt constraints numAlloc width a b).getResult σ).1.size =
  constraints.size + 1 + k*(width + 3)
:= by
  simp [check_lt]
  generalize ((mkConstant 0).getResult σ) = isLt
  generalize ((mkConstant 0).getHashConsState σ) = σ
  induction' k with k h_k generalizing isLt σ constraints numAlloc width
  . simp [check_lt_impl]
  . unfold check_lt_impl
    set a' := Vector.ofFn (λ i => a[i.castSucc])
    set b' := Vector.ofFn (λ i => b[i.castSucc])
    simp [getResult_bind]
    rewrite [h_k]
    simp [num2bits.num_constraints, isZero.num_constraints]
    grind

@[simp, grind =]
lemma check_lt_numAlloc
  {p : ℕ}
  {k}
  {constraints : Array (BoundRef p)} {numAlloc : ℕ}
  {width : ℕ}
  {a b : Vector (BoundRef p) k}
  {σ}
:
  ((check_lt constraints numAlloc width a b).getResult σ).2 =
  numAlloc + k*(num2bits.numAllocStep width + isZero.numAllocStep)
:= by
  simp [check_lt]
  generalize ((mkConstant 0).getResult σ) = isLt
  generalize ((mkConstant 0).getHashConsState σ) = σ
  induction' k with k h_k generalizing isLt σ constraints numAlloc width
  . simp [check_lt_impl]
  . unfold check_lt_impl
    set a' := Vector.ofFn (λ i => a[i.castSucc])
    set b' := Vector.ofFn (λ i => b[i.castSucc])
    simp [getResult_bind]
    rewrite [h_k]
    grind

@[simp, grind =]
lemma inner_num_constraints
  {p}
  {k}
  {constraints : Array (BoundRef p)}
  {ab t : Vector (BoundRef p) (2*k-1)}
  {p' q r}
  {σ}
:
  ((inner constraints ab t p' q r).getResult σ).size =
  constraints.size + (2*k-1)
:= by
  unfold inner
  simp [←bind_assoc, -bind_pure_comp]

  have (length) (f : ℕ → HashConsM p (BoundRef p)) :
    (((List.range length).foldrM (λ x (constraints : Array (BoundRef p)) => do
      let x ← f x
      pure (constraints.push x)
    ) constraints).getResult σ).size = constraints.size + length
  := by
    induction length
    . simp
    . simp

  rw [this]

@[simp, grind =]
lemma rangeCheckVec_num_constraints
  {p}
  {k width}
  {constraints : Array (BoundRef p)}
  {numAlloc : ℕ}
  {vec : Vector (BoundRef p) k}
  {σ}
:
  ((rangeCheckVec constraints numAlloc width vec).getResult σ).1.size =
  constraints.size + k*(width + 1)
:= by
  unfold rangeCheckVec
  obtain ⟨⟨l⟩, h_l⟩ := vec
  induction' l with x l ih generalizing k constraints numAlloc σ
  . simp
    grind
  . obtain _ | k := k
    . exfalso; grind
    simp at ⊢ ih
    rewrite [ih (k := k)]
    . simp [num2bits.num_constraints]
      grind
    . grind

@[simp, grind =]
lemma rangeCheckVec_numAlloc
  {p}
  {k width : ℕ}
  {constraints : Array (BoundRef p)}
  {numAlloc : ℕ}
  {vec : Vector (BoundRef p) k}
  {σ}
:
  ((rangeCheckVec constraints numAlloc width vec).getResult σ).2 =
  numAlloc + k * (num2bits.numAllocStep width)
:= by
  unfold rangeCheckVec
  obtain ⟨⟨l⟩, h_l⟩ := vec
  induction' l with x l ih generalizing k constraints numAlloc σ
  . simp [←h_l]
  . obtain _ | k := k
    . exfalso; grind
    simp at ⊢ ih
    rewrite [ih (k := k)]
    . simp
      grind
    . grind

@[simp, grind =]
lemma allocRangeChecked_num_constraints
  {p}
  {k width}
  {constraints : Array (BoundRef p)}
  {numAlloc : ℕ}
  {σ}
:
  ((allocRangeChecked constraints numAlloc k width).getResult σ).2.1.size =
  constraints.size + k*(width + 1)
:= by
  unfold allocRangeChecked
  simp

@[simp, grind =]
lemma allocRangeChecked_numAlloc
  {p}
  {k width}
  {constraints : Array (BoundRef p)}
  {numAlloc : ℕ}
  {σ}
:
  ((allocRangeChecked constraints numAlloc k width).getResult σ).2.2 =
  numAlloc + k * (1 + num2bits.numAllocStep width)
:= by
  unfold allocRangeChecked
  simp
  grind

@[simp, grind =]
lemma polyMult_num_constraints
  {p}
  {k}
  {constraints : Array (BoundRef p)}
  {numAlloc}
  {a b : Vector (BoundRef p) k}
  {σ : HashConsSt p}
:
  ((polyMult constraints numAlloc a b).getResult σ).2.1.size =
  constraints.size + (2*k-1)
:= by
  unfold polyMult assertPolyEqProd
  simp

@[simp, grind =]
lemma polyMult_numAlloc
  {p}
  {k}
  {constraints : Array (BoundRef p)}
  {numAlloc}
  {a b : Vector (BoundRef p) k}
  {σ : HashConsSt p}
:
  ((polyMult constraints numAlloc a b).getResult σ).2.2 =
  numAlloc + (2*k-1)
:= by
  unfold polyMult assertPolyEqProd
  simp

@[simp, grind =]
lemma num_constraints_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {width k}
  {a b p'}
  {σ : HashConsSt p}
:
  ((fpMul constraints numAlloc width k a b p').getResult σ).2.1.size =
  constraints.size + num_constraints width k
:= by
  simp [
    fpMul,
    fpMul_impl,
    rangeCheckInputs,
    num2bits.num_constraints
  ]
  obtain _ | k := k
  . simp [num_constraints]
  . rewrite [ite_cond_eq_false]
    . grind [num_constraints]
    . grind




@[simp, grind =]
lemma numAllocStep_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {width k}
  {a b p'}
  {σ : HashConsSt p}
:
  ((fpMul constraints numAlloc width k a b p').getResult σ).2.2 =
  numAlloc + numAllocStep width k
:= by
  simp [fpMul, fpMul_impl, numAllocStep, rangeCheckInputs]
  grind

end fpMul


end Bob

end ConstraintSystem

end Clap
