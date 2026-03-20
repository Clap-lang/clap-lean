import Clap.Lang

namespace Packing

open Clap.Lang

variable {p : ℕ} [Core p]
open Core

def assertIs64BitLimbs [Fact (Primes.fits p 64)] {numLimbs : ℕ}
  (a : Vector (F p) numLimbs) :
  Option Unit
:= do
  _ ← a.mapM F64.ofF
  pure ()

def assertIsBytes [Fact (Primes.fits p 8)] {numBytes : ℕ}
  (a : Vector (F p) numBytes) :
  Option Unit
:= do
  _ ← a.mapM F8.ofF
  pure ()

-- #check Vector.cons

open Classical in
example [Fact (Primes.fits p 8)] {n : ℕ} {a : Vector (F p) n} : assertIsBytes a =
    if (∀ i, ∃ n : ℕ, a.get i = n ∧ n < 256) then .some () else .none := by
  unfold assertIsBytes  F8.ofF FBitVec.ofF
  simp only [Option.pure_def, Option.bind_eq_bind]
  split_ifs with h
  · have {α : Type} {c : Option α} : c.isSome → (c.bind fun _ ↦ .some ()) = some () := by
      intros h
      refine Option.bind_eq_some_iff.mpr ?_
      use c.get h
      simp
    rw [this]
    have {n : ℕ} {α β : Type} {f : α → Option β} {a : Vector α n} : (∀ i, (f (a.get i)).isSome) → (Vector.mapM f a).isSome := by
      intros h
      induction n with
      | zero =>
        have : a = #v[] := by
          simp
        erw [this, Vector.mapM_mk_empty]
        simp
      | succ n ih =>

        unfold Vector.mapM

        sorry
    apply this
    intros i


    sorry

  · sorry

def bigEndianBits2Num : FBitVec p → F p := bits2num ∘ .reverse

def bytes2BigEndianBits [Fact (Primes.fits p 8)] {n : ℕ} (bytes : Vector (F p) n) : Option (FBitVec p) := do
  let bits ← bytes.mapM F8.ofF
  return bits.foldl (fun acc bits ↦ acc ++ bits.reverse) []

def chunksToFieldElem (numChuncks : ℕ)
  (bitsPerChunk : ℕ)
  (chunks : List (F p)) :
  F p
:=
  assert! Primes.fits p (numChuncks * bitsPerChunk)
  let base := 2^bitsPerChunk
  chunks.reverse.foldl (fun acc x ↦ acc * base + x) 0

def bigEndianBitsToScalars (bitsPerScalar : ℕ) (bits : FBitVec p) : Array (F p) :=
  assert! Primes.fits p bitsPerScalar
  assert! 0 < bitsPerScalar
  step bits 0 [] .empty
 where
  step (bits : FBitVec p) (cnt:ℕ) (tmp:List (F p)) (res : Array (F p)) : Array (F p) :=
    match bits with
    | [] =>
         res.push (bigEndianBits2Num tmp.reverse)
    | bit::bits =>
      if cnt = bitsPerScalar then
        let res := res.push (bigEndianBits2Num tmp.reverse)
        step bits 1 [bit] res
      else
      step bits (cnt+1) (bit::tmp) res

def chunksToFieldElems {numChuncks : ℕ}
  (chunksPerScalar bitsPerChunk : ℕ)
  (chunks : Vector (F p) numChuncks) :
  (Array (F p))
:=
  assert! numChuncks != 0
  assert! 0 < chunksPerScalar
  step chunks.toArray.toList 0 [] .empty
 where
  step (chunks : List (F p)) (cnt:ℕ) (tmp:List (F p)) (res : Array (F p)) : (Array (F p)) :=
    match chunks with
    | [] =>
        let x := chunksToFieldElem chunksPerScalar bitsPerChunk tmp.reverse
        res.push x
    | c::chunks =>
      if cnt = chunksPerScalar then
        let x := chunksToFieldElem chunksPerScalar bitsPerChunk tmp.reverse
        step chunks 1 [c] (res.push x)
      else
        step chunks (cnt+1) (c::tmp) res

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

example : chunksToFieldElem (p := p) 0 2 [] = 0 := by rfl
/- [00₂, 11₂, 10₂] -> 101100₂ -/
example : chunksToFieldElem (p := p) 3 2 [0, 3, 2] = 44 := by native_decide
/- Doesn't fit -/
--example : chunksToFieldElem (p := p) 1 (p.log2 + 1) [1] = none := by rfl
/-- [00₂, 11₂, 10₂, 01₂, 11₂, 10₂] -> 101100₂, 101101₂ -/

example : chunksToFieldElems (p := p) 3 2 #v[0,3,2, 1,3,2] = #[44, 45] := by
  native_decide
example :
  chunksToFieldElems (p := p) 1 2 #v[0, 3, 2, 1, 3, 2] = #[0, 3, 2, 1, 3, 2]
:= by native_decide
--example : chunksToFieldElems (p := p) 0 2 #v[0, 3, 2, 1, 3, 2] = .none := by native_decide
example : chunksToFieldElems (p := p) 3 1 #v[0, 1, 1, 1, 0, 0] = #[6, 1] := by native_decide
example : chunksToFieldElems (p := p) 3 1 #v[0, 1, 1, 1] = #[6, 1] := by native_decide

example :
  bigEndianBitsToScalars (p := p) 4 [0,0,0,0, 0,0,0,1, 0,1,1] = #[0, 1, 3]
:= by native_decide
example :
  bigEndianBitsToScalars (p := p) 4 [0,0,0,0, 0,0,0,1, 0,1,1,0] = #[0, 1, 6]
:= by native_decide
-- example :
--   bigEndianBitsToScalars (p := p) 0 [0,0,0,0, 0,0,0,1, 0,1,1,0] = .none
-- := by native_decide

end TestPacking
