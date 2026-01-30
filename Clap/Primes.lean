import Mathlib.FieldTheory.Finite.Basic -- field operations

namespace Primes

-- only for small tests and examples
instance : Fact (Nat.Prime 7) := by decide

-- one more than max u16
abbrev fermat_f4 := 65537
instance : Fact (Nat.Prime fermat_f4) := by native_decide

-- less than 32 bits
abbrev babybear := 15 * 2^27 + 1
instance : Fact (Nat.Prime babybear) := by native_decide
-- TODO norm_num seems to not be working in recent versions

-- less than 64 bits
abbrev goldilocks := (2^64) - (2^32) + 1
instance : Fact (Nat.Prime goldilocks) := by sorry

-- less than 256 bits
-- BN254 scalar field
def bn254 := 21888242871839275222246405745257275088548364400416034343698204186575808495617
instance : Fact (Nat.Prime bn254) := by sorry

end Primes
