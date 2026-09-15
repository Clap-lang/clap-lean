import Clap.eDSLState.Expr
import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.WitnessGenerator.isZero
import Clap.eDSLState.WitnessGenerator.num2bits

import CompPoly.Univariate.Basic

namespace Clap.WitnessGenerator

section FpMulImplementation

open CompPoly HashConsM

variable {p : ℕ} {var : Type} -- [inst' : Fact (p > 2)]

def toCompPoly {p k : ℕ} [inst : Fact (Nat.Prime p)] (vec : Vector (ZMod p) k) : CPolynomial (ZMod p) :=
  List.foldr (fun i p ↦ p + CPolynomial.C (vec[i]) * CPolynomial.X ^ i.1) 0 (List.finRange k)

def rangeCheckVec
  {k}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (width : ℕ) (vec : Vector ExprRef k)
: Array (ZMod p) :=
  vec.foldr (fun e trace ↦ num2bitsUnsafe cache trace width e) trace

def rangeCheckInputs
  {k}
  (cache : ValueCache p)
  (trace : Array (ZMod p))
  (width : ℕ)
  (a b p' : Vector ExprRef k)
: Array (ZMod p) :=
  let trace := rangeCheckVec cache trace width a
  let trace := rangeCheckVec cache trace width b
  let trace := rangeCheckVec cache trace width p'
  trace

def carry [inst : Fact (Nat.Prime p)] (w : ℕ) : List (ZMod p) → ZMod p → List (ZMod p)
| l :: l' :: ls, c => let c' : ZMod p := (l + c) / (2 ^ w); c' :: carry w (l' :: ls) c'
| _ :: []      , _ => []
| []           , _ => []

def insertListInCache
  (cache : ValueCache p) (trace : Array (ZMod p))
  (l : List (ZMod p))
:
  HashConsM p (ValueCache p × List (BoundRef p))
:= do
  let refs ← l.mapM .mkConstant
  let varStore := (Std.ExtTreeMap.ofArray (trace.zipIdx.map Prod.swap))
  let σ ← get
  let cache := refs.foldr (λ ref cache => Expr.evalWithCache varStore cache ⦃ref, σ⦄) cache
  return (cache, refs)

def insertVecInCache
  {k}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (vec : Vector (ZMod p) k)
:
  HashConsM p (ValueCache p × Vector (BoundRef p) k)
:= do
  let refs ← vec.mapM .mkConstant
  let varStore := (Std.ExtTreeMap.ofArray (trace.zipIdx.map Prod.swap))
  let σ ← get
  let cache := refs.foldr (λ ref cache => Expr.evalWithCache varStore cache ⦃ref, σ⦄) cache
  return (cache, refs)

def checkCarryZeroUnsafe [inst : Fact (Nat.Prime p)] {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (w : ℕ) (t : Vector ExprRef k)
: HashConsM p (Array (ZMod p)) := do
  let carry : List (ZMod p) := carry w (t.toList.map (cache[·]!.get!)) 0
  let trace := trace ++ carry
  let (cache, carry_constants) ← insertListInCache cache trace (carry.map (· + (2 ^ (w + 1) * k)))
  return carry_constants.foldr (init := trace) fun c trace ↦
    num2bitsUnsafe cache trace (w + Nat.clog 2 k + 2) c


def mkOr {p} (a b : BoundRef p) : HashConsM p (BoundRef p) := do
  (←a + b) - (←a*b)

def mkNot {p} (a : BoundRef p) : HashConsM p (BoundRef p) := do
  (←mkConstant 1) - a

def check_lt_wg' {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (w : ℕ)
  (isLt : HashConsM.BoundRef p)
  (t₀ : Vector (HashConsM.BoundRef p) k) (t₁ : Vector (HashConsM.BoundRef p) k)
: HashConsM p (ValueCache p × Array (ZMod p)) :=
  match k with
  | .zero => return (cache, trace)
  | .succ k => do
    let tδ ← t₀[Fin.last k] - t₁[Fin.last k]
    let x ←(←(←.mkConstant 1) - isLt) * (←(tδ + (←.mkConstant ((2 ^ w : ZMod p) - 1))))
    let varStore := (Std.ExtTreeMap.ofArray (trace.zipIdx.map Prod.swap))
    let cache := Expr.evalWithCache varStore cache ⦃x, ←get⦄
    let trace := num2bitsUnsafe cache trace w x

    -- The cache must contain tδ because it is a subexpression of x
    let trace := isZeroUnsafe cache trace tδ
    let isZero := trace.back!

    let isLt' ← mkOr isLt (←(←mkConstant 1) - (←mkConstant isZero))

    let varStore := (Std.ExtTreeMap.ofArray (trace.zipIdx.map Prod.swap))
    let cache := Expr.evalWithCache varStore cache ⦃isLt', ←get⦄

    check_lt_wg' cache trace w isLt' (Vector.ofFn (fun i ↦ t₀[(i.castSucc)])) (Vector.ofFn (fun i ↦ t₁[(i.castSucc)]))


def checkLtUnsafe {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (w : ℕ) (t₀ : Vector (HashConsM.BoundRef p) k) (t₁ : Vector (HashConsM.BoundRef p) k)
: HashConsM p (ValueCache p × Array (ZMod p)) := do
  check_lt_wg' cache trace w (←mkConstant 0) t₀ t₁


def polyMult [inst : Fact (Nat.Prime p)]
  {k}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (a b : Vector ExprRef k)
: CPolynomial (ZMod p) × Array (ZMod p) :=
  let ab := toCompPoly (a.map (cache[·]!.get!)) * toCompPoly (b.map (cache[·]!.get!))
  let ab_trace := Array.range (2 * k -1) |>.map ab.coeff
  (ab, trace ++ ab_trace)

def allocUncheckedUnsafe
  {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (values : Vector ExprRef k)
: Array (ZMod p) :=
  trace ++ values.toArray.map (cache[·]!.get!)

def allocRangeCheckedUnsafe
  {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (width : ℕ)
  (values : Vector ExprRef k)
: Array (ZMod p) :=
  let trace := allocUncheckedUnsafe cache trace values
  rangeCheckVec cache trace width values


def fpMulUnsafe [inst : Fact (Nat.Prime p)] {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (width : ℕ) (a b p' : Vector ExprRef k)
: HashConsM p (ValueCache p × Array (ZMod p)) := do
  let trace := rangeCheckInputs cache trace width a b p'

  let (ab, trace) := polyMult cache trace a b

  let a_val : ℕ := ∑ i : Fin k, cache[a[i]]!.get!.val * (2 ^ width) ^ i.1
  let b_val : ℕ := ∑ i : Fin k, cache[b[i]]!.get!.val * (2 ^ width) ^ i.1
  let p_val : ℕ := ∑ i : Fin k, cache[p'[i]]!.get!.val * (2 ^ width) ^ i.1
  let q_val : ℕ := (a_val * b_val) / p_val
  let r_val : ℕ := (a_val * b_val) % p_val

  let q_vec := natToLimbsV (p := p) width k q_val
  let (cache, q_vec_constants) ← insertVecInCache cache trace q_vec
  let trace := allocRangeCheckedUnsafe cache trace width q_vec_constants

  let r_vec := natToLimbsV (p := p) width k r_val
  let (cache, r_vec_constants) ← insertVecInCache cache trace r_vec
  let trace := allocRangeCheckedUnsafe cache trace width r_vec_constants

  let t := ab - toCompPoly (p'.map (cache[·]!.get!)) * toCompPoly q_vec - toCompPoly r_vec
  let (cache, t_vec_constants) ← insertVecInCache cache trace (Vector.range (2 * k - 1) |>.map t.coeff)
  let trace := allocUncheckedUnsafe cache trace t_vec_constants

  let trace ← checkCarryZeroUnsafe cache trace width t_vec_constants

  checkLtUnsafe cache trace width r_vec_constants p'

end FpMulImplementation

namespace fpMul

def trace_capacity (k width: ℕ) : ℕ :=
  3 * k * num2bits.trace_capacity width +
  (2 * k - 1) + k * (num2bits.trace_capacity width + 1) +
  k * (num2bits.trace_capacity width + 1) +
  (2 * k - 1) +
  (2 * k - 1 - 1) +
  (2 * k - 1 - 1) * num2bits.trace_capacity (width + Nat.clog 2 (2 * k - 1) + 2) +
  k * (num2bits.trace_capacity width + isZero.trace_capacity)

@[simp, grind =]
lemma rangeCheckVec_trace_size
  {p} {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width}
  {vec : Vector ExprRef k}
:
  (rangeCheckVec cache trace width vec).size = trace.size + k*num2bits.trace_capacity width
:= by
  simp [rangeCheckVec]
  induction' k with k ih generalizing trace
  . have : vec = #v[] := by grind
    simp [this]
  . have := Vector.push_pop_back vec
    rewrite [←this]
    simp
    rewrite [ih]
    grind

@[simp, grind =]
lemma rangeCheckInputs_trace_size
  {p} {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width}
  {a b p' : Vector ExprRef k}
:
  (rangeCheckInputs cache trace width a b p').size = trace.size + 3*k*num2bits.trace_capacity width
:= by
  grind [rangeCheckInputs]

@[simp, grind=]
lemma allocUncheckedUnsafe_trace_size
  {p} {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {values : Vector ExprRef k}
:
  (allocUncheckedUnsafe cache trace values).size = trace.size + k
:= by
  grind [allocUncheckedUnsafe]

@[simp, grind=]
lemma allocRangeCheckedUnsafe_trace_size
  {p} {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width}
  {values : Vector ExprRef k}
:
  (allocRangeCheckedUnsafe cache trace width values).size = trace.size + k*(num2bits.trace_capacity width + 1)
:= by
  grind [allocRangeCheckedUnsafe]

@[simp, grind =]
lemma carry_length
  {p} [Fact p.Prime]
  {width : ℕ}
  {l : List (ZMod p)}
  {c : ZMod p}
:
  (carry width l c).length = l.length - 1
:= by
  fun_induction carry
  . grind
  . grind
  . grind

@[simp, grind =]
lemma insertListInCache_length
  {p}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {list : List (ZMod p)}
  {σ}
:
  ((insertListInCache cache trace list).run σ).1.2.length =
  list.length
:= by
  simp [insertListInCache]
  induction' list with head tail ih generalizing σ cache trace
  . rfl
  . simp_rw [
      ←HashConsM.getHashConsState.eq_def,
      ←HashConsM.getResult.eq_def,
    ] at ⊢ ih
    simp

@[simp, grind =]
lemma checkCarryZeroUnsafe_trace_size
  {p} [Fact p.Prime] {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width}
  {t : Vector ExprRef k}
  {σ}
:
  ((checkCarryZeroUnsafe cache trace width t).run σ).1.size =
  trace.size +
    (k-1) +
    (k-1) * (
      num2bits.trace_capacity (width + Nat.clog 2 k + 2)
    )
:= by
  simp [
    checkCarryZeroUnsafe,
    ←HashConsM.getResult.eq_def
  ]

  set carry := carry width (List.map (fun x => cache[x]!.get!) t.toList) (0 : ZMod p)
  have h_carry_length : carry.length = k-1 := by
    grind
  clear_value carry

  obtain ⟨trace⟩ := trace
  simp

  set cache' := ((insertListInCache _ _ _).getResult σ).1
  set carry_constants := ((insertListInCache _ _ _).getResult σ).2
  have h_carry_constants : carry_constants.length = k - 1 :=  by
    subst carry_constants
    simp [HashConsM.getResult, insertListInCache_length, h_carry_length]
  clear_value cache'
  clear_value carry_constants

  obtain _ | ⟨k⟩ := k
  . grind
  . simp at *
    have : trace.length + k = (trace ++ carry).toArray.size := by grind
    rewrite [this]
    set width' := width + Nat.clog _ _ + 2
    clear_value width'
    rewrite [←h_carry_constants]
    clear this h_carry_constants h_carry_length
    induction carry_constants
    . grind
    . grind

@[simp, grind =]
lemma checkLtUnsafe_trace_size
  {p} [Fact p.Prime] {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width}
  {t1 t2 : Vector ExprRef k}
  {σ}
:
  ((checkLtUnsafe cache trace width t1 t2).run σ).1.2.size =
  trace.size + k*(num2bits.trace_capacity width + isZero.trace_capacity)
:= by
  simp [checkLtUnsafe, ←HashConsM.getResult.eq_def]
  set x := if CacheExpr.c 0 ∈ σ.exprs then _ else _
  set isLt := x.1
  set σ := x.2
  clear_value x
  clear_value isLt
  clear_value σ
  induction' k with k ih generalizing cache trace width isLt σ
  . unfold check_lt_wg'
    grind
  . unfold check_lt_wg'
    simp
    rewrite [ih]
    grind

@[simp, grind =]
lemma polyMult_size
  {p} [Fact p.Prime] {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {a b : Vector ExprRef k}
:
  (polyMult cache trace a b).2.size =
  trace.size + (2*k - 1)
:= by
  simp [polyMult]

@[simp, grind =]
lemma trace_size_eq
  {p} [Fact p.Prime] {k}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {width : ℕ}
  (a b p' : Vector ExprRef k)
  {σ}
:
  ((fpMulUnsafe cache trace width a b p').run σ).1.2.size = trace.size + trace_capacity k width
:= by
  simp [fpMulUnsafe, trace_capacity]
  grind

end Clap.WitnessGenerator.fpMul
