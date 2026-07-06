import Clap.Lang
import Clap.Wheels

/-- In the `Option` monad, mapping a total (always-`some`) function over a list always succeeds. -/
theorem list_mapM_some {α β : Type} (g : α → β) (l : List α) :
    List.mapM (m := Option) (fun a => some (g a)) l = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- In the `Option` monad, mapping a total (always-`some`) function over an array always succeeds. -/
theorem array_mapM_some {α β : Type} (g : α → β) (a : Array α) :
    Array.mapM (m := Option) (fun x => some (g x)) a = some (a.map g) := by
  rcases a with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList]
  simp [list_mapM_some]

/-- In the `Option` monad, mapping a total (always-`some`) function over a vector always succeeds. -/
theorem vector_mapM_some {α β : Type} {n : ℕ} (g : α → β) (v : Vector α n) :
    Vector.mapM (m := Option) (fun x => some (g x)) v = some (v.map g) := by
  have h := @Vector.toArray_mapM Option α β n _ _ (fun x => some (g x)) v
  rw [array_mapM_some] at h
  cases hm : Vector.mapM (m := Option) (fun x => some (g x)) v with
  | none => rw [hm] at h; simp at h
  | some w =>
    rw [hm] at h; simp at h
    apply congrArg some
    apply Vector.toArray_inj.mp
    rw [h, Vector.toArray_map]

namespace FArray

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)]

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
private def singleEndArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
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
private def leftArraySelector (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
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

/-
`oneHotRaw` always succeeds and produces the one-hot indicator of `idx`:
    position `i` is `1` exactly when `i = idx.val`.
-/
lemma oneHotRaw_eq (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    oneHotRaw len idx
      = some (Vector.ofFn fun i : Fin len => if (i : ℕ) = idx.val then (1 : F p) else 0) := by
  unfold oneHotRaw;
  convert vector_mapM_some _ _ using 2;
  rotate_right;
  use fun i => if ( i : F p ) = idx then 1 else 0;
  · ext; simp [F.eq, F.isZero_def];
    grind;
  · ext i; simp +decide [ Vector.getElem_range ] ;
    split_ifs <;> simp_all +decide [ ZMod.natCast_eq_zero_iff ];
    exact ‹¬i = idx.val› ( by rw [ ← ‹ ( i : F p ) = idx ›, ZMod.val_cast_of_lt ( by linarith ) ] )

/-
When `idx.val < len`, `singleOneArray` succeeds and is the one-hot indicator of `idx`.
-/
lemma singleOneArray_eq (len : ℕ) (idx : F p) (hlen : len ≤ p) (hidx : idx.val < len) :
    singleOneArray len idx
      = some (Vector.ofFn fun i : Fin len => if (i : ℕ) = idx.val then (1 : F p) else 0) := by
  unfold singleOneArray;
  rw [ oneHotRaw_eq len idx hlen ];
  unfold F.assert_eq; simp +decide [ hidx ] ;
  rw [ show ( Vector.foldl ( fun acc b => acc + b ) 0 ( Vector.ofFn fun i : Fin len => if ( i : ℕ ) = ZMod.val idx then ( 1 : F p ) else 0 ) ) = 1 from ?_ ] ; simp +decide [ eq0 ];
  -- The sum of the vector is 1 because there's exactly one element that's 1, and the rest are 0.
  have h_sum : (Vector.ofFn (fun i : Fin len => if i.val = idx.val then (1 : F p) else 0)).toList.sum = 1 := by
    simp +decide [ Vector.ofFn ];
    rw [ List.sum_ofFn ];
    simp +decide [ Finset.sum_ite, hidx ];
    rw [ Finset.card_eq_one.mpr ] ; aesop;
    exact ⟨ ⟨ idx.val, hidx ⟩, by ext; aesop ⟩;
  convert h_sum using 1;
  induction ( Vector.ofFn fun i : Fin len => if ( i : ℕ ) = ZMod.val idx then ( 1 : F p ) else 0 ) using Vector.recOn ; simp +decide [ * ];
  induction ‹Array ( F p ) › using Array.recOn ; simp +decide [ *, Array.sum ];
  rw [ List.foldl_eq_foldr ]

/-
`singleEndArray` always succeeds and is the one-hot indicator of `idx`
    (all zeros when `idx.val ≥ len`, which is captured by the indicator since no `i < len`
    satisfies `i = idx.val`).
-/
lemma singleEndArray_eq (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    singleEndArray len idx
      = some (Vector.ofFn fun i : Fin len => if (i : ℕ) = idx.val then (1 : F p) else 0) := by
  -- By definition of `singleEndArray`, we know that it returns the one-hot vector.
  have h_oneHot : oneHotRaw len idx = some (Vector.ofFn (fun i : Fin len => if (i : ℕ) = idx.val then (1 : F p) else 0)) := by
    exact?;
  -- By definition of `singleEndArray`, we know that it returns the one-hot vector when the condition is satisfied.
  simp [singleEndArray, h_oneHot];
  -- By definition of `Vector.foldl`, we can rewrite the left-hand side of the equation.
  have h_foldl : Vector.foldl (fun acc b => acc + b) 0 (Vector.ofFn (fun i : Fin len => if (i : ℕ) = idx.val then (1 : F p) else 0)) = ∑ i : Fin len, (if (i : ℕ) = idx.val then (1 : F p) else 0) := by
    have h_foldl : ∀ (v : Vector (F p) len), Vector.foldl (fun acc b => acc + b) 0 v = ∑ i : Fin len, v[i] := by
      intro v
      rcases v with ⟨v⟩
      induction v using Array.recOn ; simp +decide [ *, Finset.sum_range_succ' ];
      rw [ ← List.sum_eq_foldl ];
      refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
    convert h_foldl _ using 2 ; aesop;
  by_cases h : ∃ i : Fin len, ( i : ℕ ) = idx.val <;> simp_all +decide [ Finset.sum_ite ];
  · obtain ⟨ i, hi ⟩ := h; rw [ show ( Finset.filter ( fun x : Fin len => ( x : ℕ ) = ZMod.val idx ) Finset.univ : Finset ( Fin len ) ) = { i } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi ⟩, fun j hj => Fin.ext <| by aesop ⟩ ] ; simp +decide ;
    unfold F.assert_eq; simp +decide [ Clap.Spec.Compiler.eq0 ] ;
  · simp +decide [ F.assert_eq ];
    unfold eq0; aesop;

/-
`Clap.minBits` is monotone.
-/
lemma minBits_mono {a b : ℕ} (h : a ≤ b) : Clap.minBits a ≤ Clap.minBits b := by
  -- Consider two cases: $a = 0$ and $a > 0$.
  by_cases ha : a = 0;
  · unfold Clap.minBits;
    grind +qlia;
  · rw [ Clap.minBits_eq a, Clap.minBits_eq b ];
    unfold Clap.minBits';
    simp +decide [ ha, Nat.log2_eq_log_two ];
    exact Nat.lt_succ_of_le ( Nat.log_mono_right h ) |> fun x => by aesop;

/-
Invariant for the left-to-right scan inside `arraySelector`. After processing the first `m`
    indices `0,1,…,m-1`, the running bit is `1` iff `s < m ≤ e` (the start index `s` has been
    seen but the end index `e` has not yet been reached).
-/
lemma selector_fold (len s e : ℕ) (hse : s < e) :
    ∀ m, m ≤ len →
      List.foldl
        (fun (prev : F p) (i : Fin len) =>
          FB.and (FB.or prev (if (i : ℕ) = s then 1 else 0)) (FB.not (if (i : ℕ) = e then 1 else 0)))
        FB.false ((List.finRange len).take m)
      = if s < m ∧ m ≤ e then (1 : F p) else 0 := by
  intro m hm
  induction m with
  | zero => aesop
  | succ m ih =>
    rw [ List.take_add_one, List.foldl_append ];
    split_ifs <;> simp_all +decide;
    · rw [ ih ( by linarith ) ] ; split_ifs <;> simp_all +decide [ FB.or, FB.and, FB.not ];
      grind;
    · by_cases h : m = s <;> by_cases h' : m = e <;> simp_all +decide [ FB.or, FB.and ];
      · linarith;
      · exact Or.inr ( by unfold FB.not; simp +decide );
      · grind +qlia

/-
Closed form for `arraySelector`: under the size/bit hypotheses it succeeds and produces the
    `{0,1}`-valued indicator of the half-open window `[startIdx.val, endIdx.val)`.
-/
lemma arraySelector_eq (len : ℕ) (startIdx endIdx : F p)
    (hlen : len ≤ p) (hstart : startIdx.val < len)
    (hlt : startIdx.val < endIdx.val)
    (hend : endIdx.val < 2 ^ Clap.minBits len)
    (hw : 2 ^ (Clap.minBits len + 1) < p) :
    arraySelector len startIdx endIdx
      = some (Vector.ofFn fun i : Fin len =>
          if startIdx.val ≤ (i : ℕ) ∧ (i : ℕ) < endIdx.val then (1 : F p) else 0) := by
  unfold arraySelector; simp +decide [ * ] ;
  rw [ if_pos ( minBits_mono hlen ), Spec.F.lessThan_equiv ];
  · rw [ singleOneArray_eq, singleEndArray_eq ];
    · simp +decide [ FB.ofBool, FB.assert, hlt ];
      rw [ show ( eq0 FB.true.not : Option Unit ) = some () from by
            unfold eq0 FB.true FB.not; aesop; ] ; simp +decide [ Vector.ofFn ] ;
      refine' Array.ext _ _ <;> simp +decide [ Array.getElem_ofFn ];
      intro i hi₁ hi₂; convert selector_fold len startIdx.val endIdx.val hlt ( i + 1 ) ( by linarith ) using 1;
      grind;
    · linarith;
    · linarith;
    · exact hstart;
  · grind +splitImp;
  · exact hend;
  · grind

end FArray

namespace TestArray

open Clap.Lang Clap.Spec
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
