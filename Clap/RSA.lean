import Clap.Lang
import Clap.Wheels

namespace Clap.RSA

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)]

/--
`base^65537 mod modulus` on bignum operands.

Since `65537 = 2^16 + 1`, we compute `base^(2^16) · base` by unrolling 16 squarings (`fpMul` of a value by itself) and one final multiplication by `base`.
`w` = bit-width per limb, `k` = number of limbs, limbs are LSB-first in `ZMod p`, matching `fpMul`
-/
def fpPow65537Mod (w k : ℕ) (base modulus : List (F p)) : Option (List (F p)) := do
  let d15 ← (List.range 16).foldlM (fun pow _ ↦ fpMul w k pow pow modulus) base
  fpMul w k d15 base modulus

/-- RSA-2048 PKCS#1 v1.5 signature verification with public exponent `e = 65537`.
For now, just a "copy-paste" from CIRCOM

All bignums are 32 × 64-bit limbs, LSB-first (limb 0 is the lowest 64 bits),
each limb big-endian within itself. The SHA-256 hash is passed as 4 × 64-bit limbs in the same orientation.
-/
def RSA_2048_e_65537_PKCS1_V1_5_Verify
    (sha2_hash : Vector (F p) 4)
    (signature : Vector (F p) 32)
    (pubkey_modulus : Vector (F p) 32)
    : Option Unit := do
  -- "Decrypt" the signature: pm = signature^65537 mod modulus, as 32 × 64-bit limbs.
  let pm ← fpPow65537Mod 64 32 signature.toList pubkey_modulus.toList
  F.assert_eq pm[0]! sha2_hash[0]
  F.assert_eq pm[1]! sha2_hash[1]
  F.assert_eq pm[2]! sha2_hash[2]
  F.assert_eq pm[3]! sha2_hash[3]
  F.assert_eq pm[4]! (217300885422736416 : F p)
  F.assert_eq pm[5]! (938447882527703397 : F p)
  F.assert_eq pm[6]! (0xFFFFFFFF00303130 : F p)
  for i in List.range' 7 24 do F.assert_eq pm[i]! (18446744073709551615 : F p)
  F.assert_eq pm[31]! (562949953421311 : F p)

end Clap.RSA

namespace Clap.RSA.Test

open Clap.Lang RSA

/-- encode `a^65537 mod b` (computed in `ℕ`) into `k` little-endian limbs of width `w`. -/
private def refPow65537 (p : ℕ) (w k : ℕ) (a b : ℕ) : List (ZMod p) :=
  natToLimbs w k ((a ^ 65537) % b)

example :
    letI a := 2; letI b := 3
    fpPow65537Mod (p := 7) 2 1 (natToLimbs 2 1 a) (natToLimbs 2 1 b)
      = some (refPow65537 7 2 1 a b) := by native_decide

example :
    letI a := 1; letI b := 3
    fpPow65537Mod (p := 7) 2 1 (natToLimbs 2 1 a) (natToLimbs 2 1 b)
      = some (refPow65537 7 2 1 a b) := by native_decide

example :
    letI a := 3; letI b := 5
    fpPow65537Mod (p := 7) 3 1 (natToLimbs 3 1 a) (natToLimbs 3 1 b)
      = some (refPow65537 7 3 1 a b) := by native_decide

-- 2^65537 mod (2^31 - 1) — M_31 Mersenne prime, ord(2) = 31, 65537 mod 31 = 3.
example :
    letI a := 2; letI b := 2^31 - 1
    fpPow65537Mod (p := Primes.babybear) 16 2 (natToLimbs 16 2 a) (natToLimbs 16 2 b)
      = some (refPow65537 Primes.babybear 16 2 a b) := by native_decide

-- 3^65537 mod (2^31 - 1) — different base, same 32-bit modulus.
example :
    letI a := 3; letI b := 2^31 - 1
    fpPow65537Mod (p := Primes.babybear) 16 2 (natToLimbs 16 2 a) (natToLimbs 16 2 b)
      = some (refPow65537 Primes.babybear 16 2 a b) := by native_decide

-- Self-inverse: (m-1)^2 ≡ 1 (mod m) for any m, so (m-1)^65537 ≡ m-1 (65537 is odd).
-- m = 2^32 - 1 (= [2^16-1, 2^16-1]); base = m - 1 (= [2^16-2, 2^16-1]).
example :
    letI a := 2^32 - 2; letI b := 2^32 - 1
    fpPow65537Mod (p := Primes.babybear) 16 2 (natToLimbs 16 2 a) (natToLimbs 16 2 b)
      = some (refPow65537 Primes.babybear 16 2 a b) := by native_decide

-- 2^65537 mod (2^63 - 1). 2^63 ≡ 1 (mod 2^63 - 1), ord(2) = 63, 65537 mod 63 = 17.
example :
    letI a := 2; letI b := 2^63 - 1
    fpPow65537Mod (p := Primes.babybear) 16 4 (natToLimbs 16 4 a) (natToLimbs 16 4 b)
      = some (refPow65537 Primes.babybear 16 4 a b) := by native_decide

end Clap.RSA.Test
