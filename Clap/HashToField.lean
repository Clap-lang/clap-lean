import Clap.Lang
import Clap.Packing
import Clap.Poseidon.Poseidon

namespace HashToField

open Clap.Lang

abbrev p := Clap.Poseidon.p

/-
  There is a `{maxbits}` tag in keyless which seems to be set to 64.
-/
def hash64BitLimbsToField {numLimbs : ℕ}
  (input : PaddedVector F p numLimbs) :
  Option (F p)
:=
  let len := input.len
  let input := input.data
  assert! numLimbs != 0
  let w := (numLimbs + 2) / 3
  let padded : Vector (F p) (w * 3) :=
    have h : numLimbs ≤ w * 3 := by omega
    Nat.add_sub_cancel' h ▸ (input ++ Vector.replicate (w * 3 - numLimbs) (0 : F p))
  let elems := Packing.chunksToFieldElems (p := p) 3 64 padded
  let elems := elems.push len
  Clap.Poseidon.poseidonBN254 elems.toList

def hashElemsToField (input : Array (F p)) : Option (F p) := do
  assert! input.size <= 64
  let inputs₁ := input.extract 0 16
  let inputs₂ := input.extract 16 32
  let inputs₃ := input.extract 32 48
  let inputs₄ := input.extract 48 64
  let inputs := #[inputs₁, inputs₂, inputs₃, inputs₄].filter (not ·.isEmpty)
  let leaves ← inputs.mapM (fun x ↦ Clap.Poseidon.poseidonBN254 x.toList)
  Clap.Poseidon.poseidonBN254 leaves.toList

/-
TODO it's unclear if the Packing.assertIsBytes is always needed, we could move it to a precondition
TODO Comment in keyless says "Only input.len bytes are actually hashed". How/why?
TODO In keyless ChinksToFieldElems can return numBytes or numBytes+1
-/
def hashBytesToField {numBytes : ℕ}
  (input : PaddedVector F p numBytes) :
  Option (F p)
:= do
  let len := input.len
  let input := input.data
  assert! numBytes != 0
  Packing.assertIsBytes input
  let w := (numBytes + 30) / 31
  let padded : Vector (F p) (w * 31) :=
    have h : numBytes ≤ w * 31 := by omega
    Nat.add_sub_cancel' h ▸ (input ++ Vector.replicate (w * 31 - numBytes) (0 : F p))
  let elems := Packing.chunksToFieldElems (p := p) 31 8 padded
  let elems := elems.push len
  hashElemsToField elems.toArray

end HashToField

namespace TestHashToField

open HashToField
open Clap.Lang

abbrev p := Primes.bn254

private def chunk31BytesZero : Vector (F p) 31 :=
  Vector.replicate 31 0
private def chunk31BytesOne : Vector (F p) 31 :=
  Vector.append #v[1] (Vector.replicate 30 0)

example : hashBytesToField ⟨chunk31BytesZero ++ chunk31BytesOne, 31 + 31⟩ ==
  /- poseidon [poseidon [0, 1, 62]] -/
  some 13543697266444247423540702028286854389932495956928457586471762601092527495754
:= by
  native_decide

example : hashBytesToField ⟨chunk31BytesZero ++ chunk31BytesZero, 31 + 31⟩ ==
  /- poseidon [poseidon [0, 0, 62]] -/
  some 15333809665951811835835529849636018646388422529532753098753027230583179992115
:= by
  native_decide

example :
  hashElemsToField #[0, 0, 0] ==
    /- poseidon [poseidon [0,0,0]] -/
    some 9681385400934385481936708565543908657554561955376652473066345310499027876660
:= by
  native_decide

example :
  hashElemsToField (Array.replicate (3*16 + 3) 1) ==
    /-
      poseidon
        [poseidon [1..1], poseidon [1..1], poseidon [1..1], poseidon [1,1,1]]
    -/
    .some 11628121580149142260524838530806013087501953643589744849802502906921824536992
:= by
  native_decide

example :
  -- poseidon [1, 2, 48]
  hash64BitLimbsToField ⟨#v[1,0,0, 2,0,0],48⟩ == some
    9279947276585799077805428108942311632594603656807751900699542466687045499453
:= by
  native_decide

example :
  -- poseidon [2^64, 24]
  hash64BitLimbsToField ⟨#v[0,1,0],24⟩ == some
    7782062960914706371652872958958905637393708115140004884697710811622618759288
:= by
  native_decide

end TestHashToField
