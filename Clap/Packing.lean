import Clap.Lang

namespace Packing

open Clap.Lang

variable {p : ℕ} [Core p]
open Core

def assertIs64BitLimbs [Fact (Primes.fits p 64)] {numLimbs : ℕ}
  (a : Vector (F p) numLimbs) :
  Option Unit
:= do
  a.foldlM (fun () => F64.assertRange) ()

def assertIsBytes [Fact (Primes.fits p 8)] {numBytes : ℕ}
  (a : Vector (F p) numBytes) :
  Option Unit
:= do
  a.foldlM (fun () => F8.assertRange) ()

def bigEndianBits2Num : FBitVec p → F p := bits2num ∘ .reverse

def bytes2BigEndianBits [Fact (Primes.fits p 8)] {n : ℕ} (bytes : Vector (F p) n) : Option (FBitVec p) := do
  let bits ← bytes.mapM F8.ofF
  return bits.foldl (fun acc bits ↦ acc ++ bits.reverse) []

def chunksToFieldElem {numChuncks : ℕ}
  (bitsPerChunk : ℕ)
  (chunks : Vector (F p) numChuncks) :
  Option (F p)
:= do
  if ¬Primes.fits p (numChuncks * bitsPerChunk) then .none
  let base := 2^bitsPerChunk
  return chunks.reverse.foldl (fun acc x ↦ acc * base + x) 0

-- TODO (Andrei): Decide if `chunks` should be List or Vector.
def chunksToFieldElem' (numChuncks : ℕ)
  (bitsPerChunk : ℕ)
  (chunks : List (F p)) :
  Option (F p)
:= do
  if ¬Primes.fits p (numChuncks * bitsPerChunk) then .none
  let base := 2^bitsPerChunk
  return chunks.reverse.foldl (fun acc x ↦ acc * base + x) 0

def bigEndianBitsToScalars
  (bitsPerScalar : ℕ)
  (bits : FBitVec p) :
  Option (Array (F p))
:= do
  if ¬Primes.fits p bitsPerScalar then .none
  if h : 0 < bitsPerScalar then
    step bitsPerScalar h bits .empty
  else
    .none
 where
  step (bitsPerScalar : ℕ) (h₁ : 0 < bitsPerScalar)
    (bits : FBitVec p)
    (acc : Array (F p)) :
    Array (F p)
  :=
    if h₂ : bits.isEmpty then acc else
      let x := bits.take bitsPerScalar
      let x := bigEndianBits2Num x
      have : 0 < bits.length := by
        simp [List.isEmpty_iff] at h₂
        simp only [← Nat.ne_zero_iff_zero_lt, ne_eq, List.length_eq_zero_iff]
        exact h₂
      step bitsPerScalar h₁ (bits.drop bitsPerScalar) (acc.push x)
  termination_by bits.length

-- TODO (Andrei): Decide if `chunks` should be List or Vector.
def chunksToFieldElems {numChuncks : ℕ}
  (chunksPerScalar bitsPerChunk : ℕ)
  (chunks : Vector (F p) numChuncks) :
  Option (Array (F p))
:= do
  if numChuncks == 0 then .none
  if h : 0 < chunksPerScalar then
    step chunksPerScalar h chunks.toArray.toList .empty
  else
    .none
 where
  step (chunksPerScalar : ℕ) (h₁ : 0 < chunksPerScalar)
    (bits : List (F p))
    (acc : Array (F p)) :
    Option (Array (F p))
  :=
    if h₂ : bits.isEmpty then acc else do
      let x := bits.take chunksPerScalar
      let x ← chunksToFieldElem' numChuncks bitsPerChunk x
      have : 0 < bits.length := by
        simp [List.isEmpty_iff] at h₂
        simp only [← Nat.ne_zero_iff_zero_lt, ne_eq, List.length_eq_zero_iff]
        exact h₂
      step chunksPerScalar h₁ (bits.drop chunksPerScalar) (acc.push x)
  termination_by bits.length

end Packing

namespace TestPacking

open Packing
open Clap.Lang Core ZMod

abbrev p := Primes.bn254

example : assertIs64BitLimbs (p := p) #v[1, 2, 3, 4] = .some () := by native_decide
example : assertIs64BitLimbs (p := p) #v[1, 2, 3, 2^64-1] = .some () := by native_decide
example : assertIs64BitLimbs (p := p) #v[2^64] = .none := by native_decide
example : assertIs64BitLimbs (p := p) #v[1, 2, 2^64+5] = .none := by native_decide

example : assertIsBytes (p := p) #v[1, 2, 3, 4] = .some () := by native_decide
example : assertIsBytes (p := p) #v[1, 2, 3, 2^8-1] = .some () := by native_decide
example : assertIsBytes (p := p) #v[2^8] = .none := by native_decide
example : assertIsBytes (p := p) #v[1, 2, 2^8+5] = .none := by native_decide

example : bigEndianBits2Num (p := p) [] = 0 := by rfl
example : bigEndianBits2Num (p := p) [0] = 0 := by rfl
example : bigEndianBits2Num (p := p) [1, 1, 0, 0] = 12 := by rfl

example :
  bytes2BigEndianBits (p := p) #v[] = .some []
:= by native_decide
example :
  bytes2BigEndianBits (p := p) #v[1] = .some [0, 0, 0, 0, 0, 0, 0, 1]
:= by native_decide
example :
  bytes2BigEndianBits (p := p) #v[2^8-1, 1] =
    .some [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]
:= by
  native_decide
example :
  bytes2BigEndianBits (p := p) #v[2^8] = .none
:= by
  native_decide

example : chunksToFieldElem (p := p) 2 #v[] = .some 0 := by rfl
/-- [00₂, 11₂, 10₂] -> 101100₂ -/
example : chunksToFieldElem (p := p) 2 #v[0, 3, 2] = .some 44 := by native_decide
/-- Doesn't fit -/
example : chunksToFieldElem (p := p) (p.log2 + 1) #v[1] = .none := by rfl
/-- [00₂, 11₂, 10₂, 01₂, 11₂, 10₂] -> 101100₂, 101101₂ -/

example : chunksToFieldElems (p := p) 3 2 #v[0,3,2, 1,3,2] = .some #[44, 45] := by
  native_decide
example :
  chunksToFieldElems (p := p) 1 2 #v[0, 3, 2, 1, 3, 2] =.some #[0, 3, 2, 1, 3, 2]
:= by native_decide
example : chunksToFieldElems (p := p) 0 2 #v[0, 3, 2, 1, 3, 2] = .none := by native_decide
example : chunksToFieldElems (p := p) 3 1 #v[0, 1, 1, 1, 0, 0] = some #[6, 1] := by native_decide
example : chunksToFieldElems (p := p) 3 1 #v[0, 1, 1, 1] = some #[6, 1] := by native_decide

example :
  bigEndianBitsToScalars (p := p) 4 [0,0,0,0, 0,0,0,1, 0,1,1] = .some #[0, 1, 3]
:= by native_decide
example :
  bigEndianBitsToScalars (p := p) 4 [0,0,0,0, 0,0,0,1, 0,1,1,0] = .some #[0, 1, 6]
:= by native_decide
example :
  bigEndianBitsToScalars (p := p) 0 [0,0,0,0, 0,0,0,1, 0,1,1,0] = .none
:= by native_decide

end TestPacking
