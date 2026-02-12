import Clap.Primes
import Mathlib.FieldTheory.Finite.Basic

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Computes the `n` bit binary representation of `f`.
    If `n < minBits f` the result is truncated.
    If `n > minBits f` the result is padded with zeros.
-/

def num2bitsLsbPure (n : ℕ) (f : ZMod p) : List (ZMod p) :=
  match n with
  | 0 => []
  | n+1 =>
    let bit := f.val % 2
    let rem := f.val / 2
    bit::(num2bitsLsbPure n rem)

#guard num2bitsLsbPure (p := Primes.babybear) 3 1 = [1,0,0]
#guard num2bitsLsbPure (p := Primes.babybear) 3 4 = [0,0,1]
#guard num2bitsLsbPure (p := Primes.babybear) 4 1 = [1,0,0,0]

def num2bitsMsbPure (n : ℕ) (f : ZMod p) : List (ZMod p) :=
  num2bitsLsbPure n f |> List.reverse

#guard num2bitsMsbPure (p := Primes.babybear) 3 1 = [0,0,1]
#guard num2bitsMsbPure (p := Primes.babybear) 4 1 = [0,0,0,1]

def bits2num (v : List (ZMod p)) : ZMod p :=
  aux 1 0 v
where
  aux pow acc v :=
    match v with
    | [] => acc
    | b::rest =>
        let acc := acc + (b * pow)
        aux (pow * 2) acc rest

end Clap
