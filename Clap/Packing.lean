import Clap.Lang

namespace Packing

open Clap.Lang

variable {p : ℕ}

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

def bigEndianBits2Num {w} : FBitVec p w → F p := bits2numV ∘ .reverse

def bytes2BigEndianBits [Fact (Primes.fits p 8)] {n : ℕ} (bytes : Vector (F p) n) : Option (FBitVec p (n*8)) := do
  bytes.flatMapM (fun byte ↦ Vector.reverse <$> F8.ofF byte)

def chunksToFieldElem {w : ℕ}
  (bitsPerChunk : ℕ)
  (chunks : Vector (F p) w) :
  F p
:=
  assert! Primes.fits p (w * bitsPerChunk)
  let base := 2^bitsPerChunk
  chunks.reverse.foldl (fun acc x ↦ acc * base + x) 0

-- TODO is this function even used?
def bigEndianBitsToScalars {w} (bitsPerScalar : ℕ) (bits : FBitVec p (w * bitsPerScalar)) : Vector (F p) w:=
  assert! Primes.fits p bitsPerScalar
  assert! 0 < bitsPerScalar
  let tmp : Vector (FBitVec p bitsPerScalar) w := toChunks bitsPerScalar bits
  tmp.map bigEndianBits2Num

def chunksToFieldElems {w : ℕ}
  (chunksPerScalar bitsPerChunk : ℕ)
  (chunks : Vector (F p) (w * chunksPerScalar)) :
  Vector (F p) w :=
  (toChunks chunksPerScalar chunks).map
    (chunksToFieldElem bitsPerChunk)


end Packing

namespace TestPacking

open Packing
open Clap.Lang

abbrev p := Primes.bn254

example : assertIs64BitLimbs (p := p) #v[1, 2, 3, 4] = .some () := by native_decide
example : assertIs64BitLimbs (p := p) #v[1, 2, 3, 2^64-1] = .some () := by native_decide
example : assertIs64BitLimbs (p := p) #v[2^64] = .none := by native_decide
example : assertIs64BitLimbs (p := p) #v[1, 2, 2^64+5] = .none := by native_decide

example : assertIsBytes (p := p) #v[1, 2, 3, 4] = .some () := by native_decide
example : assertIsBytes (p := p) #v[1, 2, 3, 2^8-1] = .some () := by native_decide
example : assertIsBytes (p := p) #v[2^8] = .none := by native_decide
example : assertIsBytes (p := p) #v[1, 2, 2^8+5] = .none := by native_decide

example : bigEndianBits2Num (p := p) #v[] = 0 := by rfl
example : bigEndianBits2Num (p := p) #v[0] = 0 := by rfl
example : bigEndianBits2Num (p := p) #v[1, 1, 0, 0] = 12 := by native_decide

example :
  bytes2BigEndianBits (p := p) #v[] = .some #v[]
:= by native_decide
example :
  bytes2BigEndianBits (p := p) #v[1] = .some #v[0, 0, 0, 0, 0, 0, 0, 1]
:= by native_decide
example :
  bytes2BigEndianBits (p := p) #v[2^8-1, 1] =
    .some #v[1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]
:= by
  native_decide
example :
  bytes2BigEndianBits (p := p) #v[2^8] = .none
:= by
  native_decide

example : chunksToFieldElem (p := p) 2 #v[] = 0 := by rfl
/- [00₂, 11₂, 10₂] -> 101100₂ -/
example : chunksToFieldElem (p := p) 2 #v[0, 3, 2] = 44 := by native_decide
/- Doesn't fit -/
--example : chunksToFieldElem (p := p) 1 (p.log2 + 1) [1] = none := by rfl
/-- [00₂, 11₂, 10₂, 01₂, 11₂, 10₂] -> 101100₂, 101101₂ -/

example : chunksToFieldElems (p := p) (w := 2) 3 2 #v[0,3,2, 1,3,2] = #v[44, 45] := by
  native_decide
example :
  chunksToFieldElems (p := p) (w := 6) 1 2 #v[0, 3, 2, 1, 3, 2] = #v[0, 3, 2, 1, 3, 2]
:= by native_decide
--example : chunksToFieldElems (p := p) 0 2 #v[0, 3, 2, 1, 3, 2] = .none := by native_decide
example : chunksToFieldElems (p := p) (w:=2) 3 1 #v[0, 1, 1, 1, 0, 0] = #v[6, 1] := by native_decide

example :
  bigEndianBitsToScalars (p := p) 4 #v[0,0,0,0, 0,0,0,1, 0,0,1,1] = #v[0, 1, 3]
:= by native_decide
example :
  bigEndianBitsToScalars (p := p) 4 #v[0,0,0,0, 0,0,0,1, 0,1,1,0] = #v[0, 1, 6]
:= by native_decide
-- example :
--   bigEndianBitsToScalars (p := p) 0 [0,0,0,0, 0,0,0,1, 0,1,1,0] = .none
-- := by native_decide

end TestPacking
