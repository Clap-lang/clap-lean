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


end TestHashToField
