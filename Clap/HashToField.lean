import Clap.Lang
import Clap.Packing
import Clap.Poseidon.Poseidon

namespace HashToField

open Clap.Lang

abbrev p := Clap.Poseidon.p
open Core

variable [Core p]

-- Stolen from Poseidon.lean
private def liftArr (xs : Array (ZMod p)) : Array (F p) := xs.map const
private def liftMat (xs : Array (Array (ZMod p))) : Array (Array (F p)) := xs.map (·.map const)

def hash64BitLimbsToFieldWithLen {numLimbs : ℕ}
  (input : Vector (F p) numLimbs)
  (len : ℕ)
  (_ : len > 0):
  Option (F p)
:= do
  let elems ← Packing.chunksToFieldElems (p := p) 3 64 input
  let elems := elems.push len
  let t := elems.size + 1
  let C ← Clap.Poseidon.Constant.C[t-2]?
  let S ← Clap.Poseidon.Constant.S[t-2]?
  let M ← Clap.Poseidon.Constant.M[t-2]?
  let P ← Clap.Poseidon.Constant.P[t-2]?
  let e ←
    Clap.Poseidon.poseidon
      elems
      (liftArr C)
      (liftArr S)
      (liftMat M)
      (liftMat P)
  pure e

end HashToField

namespace TestHashToField

open HashToField
open Clap.Lang Core ZMod


end TestHashToField
