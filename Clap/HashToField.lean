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

end HashToField

namespace TestHashToField

open HashToField
open Clap.Lang Core ZMod

abbrev p := Primes.bn254

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
