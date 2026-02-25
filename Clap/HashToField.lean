import Clap.Lang
import Clap.Packing
import Clap.Poseidon.Poseidon

namespace HashToField

open Clap.Lang

abbrev p := Clap.Poseidon.p

open Core

variable [Core p]

/-
  `inputMaxbits` corresponds to the `{maxbits}` tag. Circom tags are assigned
  values known at compile time.
-/
def hash64BitLimbsToFieldWithLen {numLimbs : ℕ}
  (input : Vector (F p) numLimbs)
  (inputMaxbits : ℕ)
  (len : F p) :
  Option (F p)
:= do
  if inputMaxbits > 64 || numLimbs == 0 then .none
  let elems ← Packing.chunksToFieldElems (p := p) 3 64 input
  let elems := elems.push len
  Clap.Poseidon.poseidonBN254 elems

def hashElemsToField (input : Array (F p)) : Option (F p) := do
  if input.size > 64 then .none
  let inputs₁ := input.extract 0 16
  let inputs₂ := input.extract 16 32
  let inputs₃ := input.extract 32 48
  let inputs₄ := input.extract 48 64
  let inputs := #[inputs₁, inputs₂, inputs₃, inputs₄].filter (not ·.isEmpty)
  let leaves ← inputs.mapM Clap.Poseidon.poseidonBN254
  Clap.Poseidon.poseidonBN254 leaves

def hashBytesToFieldWithLen {numBytes : ℕ}
  (input : Vector (F p) numBytes)
  (len : F p) :
  Option (F p)
:= do
  if numBytes == 0 then .none
  Packing.assertIsBytes input
  let elems ← Packing.chunksToFieldElems (p := p) 31 8 input
  let elems := elems.push len
  hashElemsToField elems

end HashToField

namespace TestHashToField

open HashToField
open Clap.Lang Core ZMod

abbrev p := Primes.bn254

private def chunk31BytesZero : Vector (F p) 31 :=
  Vector.replicate 31 0
private def chunk31BytesOne : Vector (F p) 31 :=
  Vector.append #v[1] (Vector.replicate 30 0)

example : hashBytesToFieldWithLen (chunk31BytesZero ++ chunk31BytesOne) (31 + 31) ==
  /- poseidon [poseidon [0, 1, 62]] -/
  some 13543697266444247423540702028286854389932495956928457586471762601092527495754
:= by
  native_decide

example : hashBytesToFieldWithLen (chunk31BytesZero ++ chunk31BytesZero) (31 + 31) ==
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
  hash64BitLimbsToFieldWithLen #v[1,0,0, 2,0,0] 64 48 ==
    some 9279947276585799077805428108942311632594603656807751900699542466687045499453
:= by
  native_decide

example :
  -- poseidon [2^64, 24]
  hash64BitLimbsToFieldWithLen #v[0,1,0] 64 24 ==
    .some 7782062960914706371652872958958905637393708115140004884697710811622618759288
:= by
  native_decide

end TestHashToField
