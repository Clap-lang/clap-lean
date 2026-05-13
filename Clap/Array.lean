import Clap.Lang
import Clap.Wheels
import Std.Do

namespace FArray

open Clap.Lang Core

variable {p : ℕ} [Core p]

/-- Computes a candidate one-hot mask: position `i` is `isZero(idx - i)`. -/
private def oneHotRaw (len : ℕ) (idx : F p) : Option (Vector (FB p) len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ F.eq idx i)

/-- Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere. Only satisfiable when `0 ≤ idx < len`. -/
def singleOneArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let out ← oneHotRaw len idx
  let s : F p := out.foldl (fun acc b ↦ acc + b) 0
  F.assert_eq s 1
  return out

/-- (SingleNegOneArray) Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere.
    Returns all zeros when `idx ≥ len`. -/
def singleEndArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let out ← oneHotRaw len idx
  let s : F p := out.foldl (fun acc b ↦ acc + b) 0
  F.assert_eq s (s * s) -- s² = s (at most one-hot)
  return out

/-- Outputs a bit array with 1s at `[startIdx, endIdx)` and 0s elsewhere.
    Satisfiable when `startIdx < endIdx` and `startIdx < len`. If `endIdx ≥ len`, the bit array has 1s at `[startIdx, len)`. -/
def arraySelector (len : ℕ) (startIdx endIdx : F p) : Option (Vector (FB p) len) := do
  let w := Clap.minBits len
  assert! w ≤ Clap.minBits p
  FB.assert (← F.lessThan w startIdx endIdx)
  let startMask ← singleOneArray len startIdx
  let endMask ← singleEndArray len endIdx
  -- At each position, turn on at startIdx (OR with startMask) and turn off at endIdx (AND with NOT endMask).
  let step (prev : FB p) (i : Fin len) : FB p := FB.and (FB.or prev startMask[i]) (FB.not endMask[i])
  -- Build the output by scanning `step` left-to-right through indices 0..i for each position i.
  return Vector.ofFn fun i ↦ (List.finRange len).take (i.1 + 1) |>.foldl step FB.false

/-- Returns the element of `arr` at index `idx`. Fails when `idx ≥ len`. -/
def selectArrayValue {len : ℕ} (arr : Vector (F p) len) (idx : F p) : Option (F p) := do
  let hot ← singleOneArray len idx
  return F.dotProduct hot arr

/-- Outputs a bit array with 1s at `[0, idx)` and 0s at `[idx, len)`. Only satisfiable when `0 ≤ idx < len`. Requires `len > 0`. -/
def leftArraySelector (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let bits ← singleOneArray len idx
  return bits.scanr (· + ·) 0

/-- Outputs a bit array with 0s at `[0, idx]` and 1s at `(idx, len)`. Only satisfiable when `0 ≤ idx < len`. -/
def rightArraySelector (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let bits ← singleOneArray len idx
  return bits.scanl (· + ·) 0

/-- Like `arraySelector`, but returns all zeros when `endIdx ≤ startIdx`. Does not work when `startIdx = 0`. -/
def arraySelectorComplex (len : ℕ) (startIdx endIdx : F p) : Option (Vector (FB p) len) := do
  FB.assert (FB.not (←isZero startIdx))
  let right ← rightArraySelector len (startIdx - 1)
  let left ← leftArraySelector len endIdx
  return right.zipWith (· * ·) left

section Specs

open Std.Do

variable [DecidableEq (F p)]

axiom isZero_spec (e : F p) :
  ⦃⌜True⌝⦄ isZero e ⦃⇓ v => ⌜v = (if e = 0 then 1 else 0)⌝⦄

axiom eq0_spec (e : F p) :
  ⦃⌜True⌝⦄ eq0 e ⦃ post⟨ fun _ => ⌜e = 0⌝, fun _ => ⌜e ≠ 0⌝ ⟩ ⦄

/-- position `i` is `1` iff `idx` equals the field embedding of `i`. -/
def oneHotVec (len : ℕ) (idx : F p) : Vector (FB p) len :=
  Vector.ofFn fun (i : Fin len) => if idx = (i.val : F p) then 1 else 0

def isBinaryVec {len : ℕ} (v : Vector (FB p) len) : Prop := ∀ i : Fin len, v[i] = 0 ∨ v[i] = 1

def oneHotSum (len : ℕ) (idx : F p) : F p := (oneHotVec len idx).foldl (· + ·) 0

-- the embedding ℕ → F p is injective on [0, len).
-- at abstract Core p level, we know nothing about the field's characteristic the map ℕ → F p is not automatically injective.
-- we can have modular wraparound and small characteristic field
def natCastInjOn (len : ℕ) : Prop := ∀ i j : Fin len, ((i.val : F p) = (j.val : F p)) → i = j

@[simp]
theorem oneHotVec_getElem {len : ℕ} (idx : F p) (i : Fin len) :
    (oneHotVec len idx)[i] = (if idx = (i.val : F p) then 1 else 0) := by
  simp [oneHotVec]

@[simp]
theorem isBinaryVec_oneHotVec (len : ℕ) (idx : F p) : isBinaryVec (oneHotVec len idx) :=
by
  intro i
  rw [oneHotVec_getElem]
  split <;> simp

omit [DecidableEq (F p)] in
/-- `assert_eq`: succeeds iff its two arguments are equal in `F p`. -/
theorem F.assert_eq_spec (a b : F p) :
  ⦃⌜True⌝⦄ F.assert_eq a b ⦃ post⟨ fun _ => ⌜a = b⌝, fun _ => ⌜a ≠ b⌝ ⟩ ⦄ := by
  unfold F.assert_eq
  mvcgen [eq0_spec]
  all_goals simp [sub_eq_zero]

/-- `eq`: returns `1` when the two arguments are equal in `F p`, otherwise `0`. -/
@[spec]
theorem F.eq_spec (a b : F p) :
  ⦃⌜True⌝⦄ F.eq a b ⦃⇓ v => ⌜v = (if a = b then 1 else 0)⌝⦄ := by
  unfold F.eq
  mvcgen [isZero_spec]
  all_goals simp [sub_eq_zero]

section -- some extra mvcgen lemmas
open Std.Do

/-- xtract `x = some b` from an Option Hoare triple `⦃⌜True⌝⦄ x ⦃⇓ v => ⌜v = b⌝⦄`. -/
private lemma option_triple_eq {β : Type} {x : Option β} {b : β}
    (h : ⦃⌜True⌝⦄ x ⦃⇓ v => ⌜v = b⌝⦄) : x = some b := by
  apply Option.of_wp_eq rfl (fun y => y = some b)
  refine Triple.entails_wp_of_post h ?_
  refine ⟨?_, ?_⟩
  · intro a; exact SPred.pure_mono (congrArg some)
  · exact ExceptConds.entails_false

/-- given `hf : ∀ a, ⦃True⦄ f a ⦃⇓ v => v = q a⦄`, the whole `mapM` returns `some (xs.map q)`. -/
@[spec]
private theorem Vector_mapM_via_spec
    {α β : Type} {n : ℕ}
    {f : α → Option β} {q : α → β}
    (xs : Vector α n)
    (hf : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ v => ⌜v = q a⌝⦄) :
    ⦃⌜True⌝⦄ xs.mapM f ⦃⇓ v => ⌜v = xs.map q⌝⦄ := by
  have hfun : f = (fun a => pure (q a)) := funext fun a => option_triple_eq (hf a)
  rw [hfun, Vector.mapM_pure]
  exact Triple.pure _ (SPred.pure_intro rfl)
end

-- because of modular aspect of the field we could have some wraparound, ie, many idx = (i.val : F p). We can't differentiate at this level
-- we refine later in singleOneArray
theorem oneHotRaw_spec (len : ℕ) (idx : F p) :
  ⦃⌜True⌝⦄ oneHotRaw len idx ⦃⇓ v => ⌜v = oneHotVec len idx ∧ isBinaryVec v⌝⦄ := by
  unfold oneHotRaw
  mvcgen
  case q => exact fun (i : ℕ) => if idx = (i : F p) then 1 else 0
  case vc2.hf.success => exact id
  case vc3.success =>
    intro hr; subst hr
    refine ⟨?_, ?_⟩
    · apply Vector.ext; intro i hi; simp [oneHotVec]
    · intro i; simp; tauto

/-- succeeds with `oneHotVec` iff `oneHotSum = 1`; else fails. -/
-- This spec still does not garantee uniqueness of 1 in the output of singleOneArray because we don't know if the field is well behaved.
-- Example: F p of characteristic 5, len = 26, idx = 0.
-- The matching set {i : Fin 26 | idx = (i.val : F 5)} = {i | (i.val : F 5) = 0} = {0, 5, 10, 15, 20, 25} 6 elements
-- 6 ≡ 1 mod 5. oneHotSum = 1 holds, singleOneArray returns some v, but v has six 1s not one.
-- See singleOneArray_uniqueOne
theorem singleOneArray_spec (len : ℕ) (idx : F p) :
  ⦃⌜True⌝⦄
    singleOneArray len idx
  ⦃ post⟨
      fun v => ⌜v = oneHotVec len idx
                ∧ oneHotSum len idx = 1
                ∧ isBinaryVec v⌝,
      fun _ => ⌜oneHotSum len idx ≠ 1⌝
    ⟩ ⦄ := by
  unfold singleOneArray
  mvcgen [oneHotRaw_spec, F.assert_eq_spec]
  all_goals simp_all [oneHotSum]

/-- If no index in `Fin len` matches `idx` in `F p`, the field-level one-hot sum is `0`. -/
private theorem oneHotSum_zero_of_no_match (len : ℕ) (idx : F p)
    (h : ∀ i : Fin len, idx ≠ (i.val : F p)) : oneHotSum len idx = 0 := by
  induction len with
  | zero => rfl
  | succ n ih =>
    have hexp : oneHotVec (n+1) idx = (oneHotVec n idx).push (if idx = ((n : ℕ) : F p) then (1 : F p) else 0) := by
      unfold oneHotVec; rw [Vector.ofFn_succ]; congr 1
    show (oneHotVec (n+1) idx).foldl (· + ·) 0 = 0
    rw [hexp, Vector.foldl_push, if_neg (h ⟨n, by omega⟩), add_zero]
    exact ih (fun i => h i.castSucc)

/-- Under injectivity of `ℕ → F p` on `[0, len)`, `singleOneArray` returning `some v` means exactly one position of `v` is `1` -/
theorem singleOneArray_uniqueOne {len : ℕ} (idx : F p) (hInj : natCastInjOn (p := p) len)
    {v : Vector (FB p) len} (h : singleOneArray len idx = some v) :
    ∃ i : Fin len,
      idx = (i.val : F p)
      ∧ v[i] = 1
      ∧ ∀ j : Fin len, j ≠ i → v[j] = 0 := by
  -- extract spec consequences
  obtain ⟨rfl, hsum, _⟩ : v = oneHotVec len idx ∧ oneHotSum len idx = 1 ∧ isBinaryVec v := by
    apply Option.of_wp_eq h (fun y => match y with
      | some b => b = oneHotVec len idx ∧ oneHotSum len idx = 1 ∧ isBinaryVec b
      | none => oneHotSum len idx ≠ 1)
    exact singleOneArray_spec len idx
  -- matching index exists, otherwise `oneHotSum = 0`, contradicting `hsum`.
  obtain ⟨i, hi⟩ : ∃ i : Fin len, idx = (i.val : F p) := by
    by_contra h_no
    have h_no' : ∀ i : Fin len, idx ≠ (i.val : F p) := by
      intro i hi
      exact h_no ⟨i, hi⟩
    rw [oneHotSum_zero_of_no_match len idx h_no'] at hsum
    exact one_ne_zero hsum.symm
  refine ⟨i, hi, ?_, fun j hji => ?_⟩
  · simp [oneHotVec, hi]
  · have hne : idx ≠ (j.val : F p) := by
      intro hc
      apply hji
      exact (hInj i j (hi.symm.trans hc)).symm
    simp [oneHotVec, hne]

end Specs

end FArray

namespace TestArray

open Clap.Lang Core Clap.Spec ZMod
open Array

abbrev p := Primes.goldilocks

abbrev p' := 11
local instance : Fact (Nat.Prime p') := by decide

-- singleOneArray tests
-- from https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/arrays/SingleOneArray.circom
-- Only satisfiable when 0 <= idx < LEN.
example : FArray.singleOneArray (p := p) 4 0 = some #v[1,0,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 1 = some #v[0,1,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 2 = some #v[0,0,1,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 3 = some #v[0,0,0,1] := by native_decide
example : FArray.singleOneArray (p := p) 6 3 = some #v[0,0,0,1,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 1 0 = some #v[1] := by native_decide
example : FArray.singleOneArray (p := p) 4 4 = none := by native_decide
example : FArray.singleOneArray (p := p) 4 5 = none := by native_decide
example : FArray.singleOneArray (p := p) 1 1 = none := by native_decide

-- singleEndArray (SingleNegOneArray) tests
-- from https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/arrays/SingleNegOneArray.circom
-- Returns a vector of all zeros when idx >= LEN.
-- @warning behaves differently than SingleOneArray: i.e., remains satisfiable even when idx > LEN
example : FArray.singleEndArray (p := p) 4 0 = some #v[1,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 2 = some #v[0,0,1,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 3 = some #v[0,0,0,1] := by native_decide
example : FArray.singleEndArray (p := p) 4 4 = some #v[0,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 5 = some #v[0,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 1 = some #v[0,1,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 1 0 = some #v[1] := by native_decide
example : FArray.singleEndArray (p := p) 6 3 = some #v[0,0,0,1,0,0] := by native_decide
-- With p' = 11, len > p causes index collisions mod p, producing s ≥ 2 which fails s² = s.
example : FArray.singleEndArray (p := p') 12 0 = none := by native_decide
example : FArray.singleEndArray (p := p') 13 1 = none := by native_decide

-- arraySelector tests
example : FArray.arraySelector (p := p) 4 0 1 = some #v[1,0,0,0] := by native_decide
example : FArray.arraySelector (p := p) 4 1 3 = some #v[0,1,1,0] := by native_decide
example : FArray.arraySelector (p := p) 4 3 4 = some #v[0,0,0,1] := by native_decide
example : FArray.arraySelector (p := p) 4 0 4 = some #v[1,1,1,1] := by native_decide
example : FArray.arraySelector (p := p) 4 2 4 = some #v[0,0,1,1] := by native_decide
example : FArray.arraySelector (p := p) 4 1 2 = some #v[0,1,0,0] := by native_decide
example : FArray.arraySelector (p := p) 4 3 3 = none := by native_decide
example : FArray.arraySelector (p := p) 4 0 0 = none := by native_decide

-- selectArrayValue tests
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 0 = some 10 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 1 = some 20 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 2 = some 30 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 3 = some 40 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 4 = none := by native_decide
example : FArray.selectArrayValue (p := p) #v[42] 0 = some 42 := by native_decide
example : FArray.selectArrayValue (p := p) #v[42] 1 = none := by native_decide
example : FArray.selectArrayValue (p := p) #v[100,200,300,400,500,600] 5 = some 600 := by native_decide

-- leftArraySelector tests
-- LeftArraySelector(4)(0) -> 0000
example : FArray.leftArraySelector (p := p) 4 0 = some #v[0,0,0,0] := by native_decide
-- LeftArraySelector(4)(1) -> 1000
example : FArray.leftArraySelector (p := p) 4 1 = some #v[1,0,0,0] := by native_decide
-- LeftArraySelector(4)(2) -> 1100
example : FArray.leftArraySelector (p := p) 4 2 = some #v[1,1,0,0] := by native_decide
-- LeftArraySelector(4)(3) -> 1110
example : FArray.leftArraySelector (p := p) 4 3 = some #v[1,1,1,0] := by native_decide
-- idx >= len fails (singleOneArray not satisfiable)
example : FArray.leftArraySelector (p := p) 4 4 = none := by native_decide

-- rightArraySelector tests
-- RightArraySelector(4)(0) -> 0111
example : FArray.rightArraySelector (p := p) 4 0 = some #v[0,1,1,1] := by native_decide
-- RightArraySelector(4)(1) -> 0011
example : FArray.rightArraySelector (p := p) 4 1 = some #v[0,0,1,1] := by native_decide
-- RightArraySelector(4)(2) -> 0001
example : FArray.rightArraySelector (p := p) 4 2 = some #v[0,0,0,1] := by native_decide
-- RightArraySelector(4)(3) -> 0000
example : FArray.rightArraySelector (p := p) 4 3 = some #v[0,0,0,0] := by native_decide
-- idx >= len fails
example : FArray.rightArraySelector (p := p) 4 4 = none := by native_decide

-- arraySelectorComplex tests
-- right(0)=[0,1,1,1] * left(2)=[1,1,0,0] = [0,1,0,0]
example : FArray.arraySelectorComplex (p := p) 4 1 2 = some #v[0,1,0,0] := by native_decide
-- right(1)=[0,0,1,1] * left(3)=[1,1,1,0] = [0,0,1,0]
example : FArray.arraySelectorComplex (p := p) 4 2 3 = some #v[0,0,1,0] := by native_decide
-- right(0)=[0,1,1,1] * left(3)=[1,1,1,0] = [0,1,1,0]
example : FArray.arraySelectorComplex (p := p) 4 1 3 = some #v[0,1,1,0] := by native_decide
-- endIdx <= startIdx → all zeros: right(1)=[0,0,1,1] * left(1)=[1,0,0,0] = [0,0,0,0]
example : FArray.arraySelectorComplex (p := p) 4 2 1 = some #v[0,0,0,0] := by native_decide
-- startIdx = 0 fails
example : FArray.arraySelectorComplex (p := p) 4 0 2 = none := by native_decide

end TestArray
