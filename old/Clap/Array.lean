import Clap.Lang
import Clap.Wheels

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
