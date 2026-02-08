import Mathlib.FieldTheory.Finite.Basic -- field operations

namespace Primes

/-- Computes the maximum power of 2 that can fit into the input. -/
def maxPow2 (x : ℕ) : ℕ :=
  2^(Nat.log2 x |> Nat.log2)

def fits (x max:ℕ) : Bool :=
  maxPow2 x ≥ max

-- only for small tests and examples
instance : Fact (Nat.Prime 7) := by decide

-- one more than max u16
abbrev fermat_f4 := 65537
instance : Fact (Nat.Prime fermat_f4) := by native_decide

-- less than 32 bits
abbrev babybear := 15 * 2^27 + 1
instance : Fact (Nat.Prime babybear) := by native_decide
-- TODO norm_num seems to not be working in recent versions
instance : Fact (fits babybear 16) := by decide

-- less than 64 bits
abbrev goldilocks := (2^64) - (2^32) + 1
instance : Fact (Nat.Prime goldilocks) := by sorry
instance : Fact (fits goldilocks 16) := by decide
instance : Fact (fits goldilocks 32) := by decide

-- less than 256 bits
-- BN254 scalar field
def bn254 := 21888242871839275222246405745257275088548364400416034343698204186575808495617
instance : Fact (Nat.Prime bn254) := by sorry
instance : Fact (fits bn254 16) := by decide
instance : Fact (fits bn254 32) := by decide
instance : Fact (fits bn254 128) := by decide

instance {p:ℕ}: ToString (ZMod p) where
  toString z := toString z.val

end Primes
