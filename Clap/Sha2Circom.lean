import Clap.Primes
import Clap.Spec
import Clap.SpecUint
import Clap.Sha2

open Clap.Spec

section Wheels

def minBits (x : ℕ) : ℕ :=
  let nb := Nat.log2 x
  if 2^nb ≤ x then nb + 1 else nb

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

end Wheels

namespace Clap.Sha2.Circom

variable {p : ℕ} [Fact (Nat.Prime p)]

@[inline]
def decompose (b l x : ℕ) : List (ZMod p) :=
  let d : ℕ := x / b
  let r : ℕ := x % b
  if l = 0 then [] else r :: (decompose b (l - 1) d)

@[reducible]
def decomposeBits : ℕ → ℕ → List (ZMod p) := decompose 2

@[reducible]
def decomposeBytes : ℕ → ℕ → List (ZMod p) := decompose 256

abbrev FBitVec8 p := List (ZMod p)

namespace FBitVec8

/-- x < 2^8. output in LSB -/
def ofUInt8Nat : ℕ → FBitVec8 p := decomposeBits 8

/-- Any ℕ. output in LSB -/
def ofNat (x : ℕ) (l : ℕ) : Array (FBitVec8 p) :=
  decomposeBytes (p := p) x l |>.map ofUInt8Nat |>.toArray

def fromString (s : String) : Array (FBitVec8 p) :=
  let bs : ByteArray := s.toUTF8
  let bs : Array UInt8 := bs.data
  bs.map (ofUInt8Nat ∘ UInt8.toNat)

end FBitVec8

instance : Inhabited (FBitVec8 p) := ⟨List.replicate 8 0⟩
instance (n : ℕ) : OfNat (FBitVec8 p) n := ⟨FBitVec8.ofUInt8Nat n⟩
instance (n : ℕ) : OfNat (Array (FBitVec8 p)) n := ⟨FBitVec8.ofNat n (minBytes n)⟩
instance : Coe UInt8 (FBitVec8 p) := ⟨FBitVec8.ofUInt8Nat ∘ UInt8.toNat⟩
instance : Coe ℕ (Array (FBitVec8 p)) := ⟨fun n ↦ FBitVec8.ofNat n (minBytes n)⟩
instance : Coe ℕ (FBitVec8 p) := ⟨FBitVec8.ofUInt8Nat⟩
instance : ShaU8 (FBitVec8 p) := ⟨FBitVec8.ofNat, FBitVec8.fromString⟩

abbrev FBitVec32 p := List (ZMod p)

namespace FBitVec32

/-- x < 2^32. output in LSB -/
def ofUInt32Nat : ℕ → FBitVec32 p := decomposeBits 32

-- x in LSB, so we just append the rest of the bits
def ofFBitVec8 (x : FBitVec8 p) : FBitVec32 p :=
  x ++ List.replicate 24 0

def toNat : FBitVec32 p → ℕ :=
  List.foldr (fun b acc => acc * 2 + b) 0

-- Constants
def zero : FBitVec32 p := List.replicate 32 0

def bv256 : FBitVec32 p := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/--
  Adds two FBitVec32 numbers using ripple-carry addition.
  Inputs: a, b: FBitVec32 p (LSB first).
  Output: FBitVec32 p - sum of a and b (modulo 2^32).
  Iterates through bits from LSB to MSB, tracking a carry bit.
-/
def add (a b : FBitVec32 p) : FBitVec32 p :=
  aux a b 0
where
  aux a b c :=
    match a, b with
    | [], [] => []
    | x :: xs, y :: ys =>
      let s := x.val + y.val + c
      let b := s % 2
      let c := s / 2
      b :: aux xs ys c
    | _, _ => []

/--
  Subtracts two FBitVec32 numbers using ripple-borrow subtraction.
  Inputs: a, b: FBitVec32 p (LSB first).
  Output: FBitVec32 p - result of a - b (modulo 2^32).
  Iterates through bits from LSB to MSB. Computes `x - y - borrow`.
  If the result is negative, adds 2 to the current bit and sets the borrow for the next bit.
-/
def sub (a b : FBitVec32 p) : FBitVec32 p :=
  aux a b 0
where
  aux a b borrow :=
    match a, b with
    | [], [] => []
    | x :: xs, y :: ys =>
      let yBorrow := y.val + borrow
      let (b, nb) := if x.val >= yBorrow then (x.val - yBorrow, 0)
                     else (x.val + 2 - yBorrow, 1)
      b :: aux xs ys nb
    | _, _ => []

/--
  Multiplies two FBitVec32 numbers using shift-and-add algorithm.
  Inputs: a, b: FBitVec32 p (LSB first).
  Output: FBitVec32 p - product of a and b (modulo 2^32).
  Iterates through the bits of `b`. If the current bit is 1, adds the current `shifted_a` to the accumulator.
  In each step, `shifted_a` is left-shifted by 1 position (0 inserted at LSB).
  The result is truncated to 32 bits to simulate wrapping behavior.
-/
def mul (a b : FBitVec32 p) : FBitVec32 p :=
  aux a b zero
where
  aux shifted_a b_bits acc :=
    match b_bits with
    | [] => acc
    | b :: bs =>
      let new_acc := if b.val = 1 then add acc shifted_a else acc
      let next_a := (0 :: shifted_a).take 32
      aux next_a bs new_acc

def ofAFBitVec8 (bs : Array (FBitVec8 p)) : FBitVec32 p :=
  bs.foldl (fun acc b ↦ (acc.mul bv256).add b) zero

/--
  Shifts bits to the right by `n` positions.
  Inputs: x (FBitVec32 p) - value to shift; n (ℕ) - number of positions to shift right.
  Output: FBitVec32 p - shifted value (zeros inserted at MSB).
  Drops the first `n` elements (LSBs) and appends `n` zeros to the end (MSBs) to maintain the fixed 32-bit length.
  Obs: this follows the behavior of `>>>` operator in Nat, not UInt32. It appears to be equivalent with
  https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/shift.circom
-/
def shr (x : FBitVec32 p) (n : ℕ) : FBitVec32 p :=
  (x.drop n) ++ (List.replicate n 0)

def shl (x : FBitVec32 p) (n : ℕ) : FBitVec32 p :=
  (List.replicate n 0 ++ x).take 32

def and (a b : FBitVec32 p) : FBitVec32 p :=
  a.zip b |>.map (fun (a,b) ↦ a * b)

def or (a b : FBitVec32 p) : FBitVec32 p :=
  a.zip b |>.map (fun (a,b) ↦ a + b - a*b)

def not (a : FBitVec32 p) : FBitVec32 p :=
  a |>.map (fun a ↦ 1 + a - 2*a)

end FBitVec32

instance : Inhabited (FBitVec32 p) := ⟨FBitVec32.zero⟩
instance (n : ℕ) : OfNat (FBitVec32 p) n := ⟨FBitVec32.ofUInt32Nat n⟩
instance : Coe (FBitVec8 p) (FBitVec32 p) := ⟨FBitVec32.ofFBitVec8⟩
instance : Coe ℕ (FBitVec32 p) := ⟨FBitVec32.ofUInt32Nat⟩

instance : Add (FBitVec32 p) := ⟨FBitVec32.add⟩
instance : Sub (FBitVec32 p) := ⟨FBitVec32.sub⟩
instance : Mul (FBitVec32 p) := ⟨FBitVec32.mul⟩
instance : HShiftRight (FBitVec32 p) ℕ (FBitVec32 p) := ⟨FBitVec32.shr⟩
instance : HShiftLeft (FBitVec32 p) ℕ (FBitVec32 p) := ⟨FBitVec32.shl⟩

section Tests

abbrev FBitVec32.add' := @FBitVec32.add Primes.babybear
abbrev FBitVec32.sub' := @FBitVec32.sub Primes.babybear
abbrev FBitVec32.mul' := @FBitVec32.mul Primes.babybear
abbrev FBitVec32.shr' := @FBitVec32.shr Primes.babybear
abbrev FBitVec32.shl' := @FBitVec32.shl Primes.babybear
abbrev ofNat32 := @FBitVec32.ofUInt32Nat Primes.babybear

#guard (FBitVec32.add' 30 30).toNat                                      = (30 + 30 : UInt32).toNat
#guard (FBitVec32.add' 0 0).toNat                                        = (0 + 0 : UInt32).toNat
#guard (FBitVec32.add' 1 0).toNat                                        = (1 + 0 : UInt32).toNat
#guard (FBitVec32.add' 0 1).toNat                                        = (0 + 1 : UInt32).toNat
#guard (FBitVec32.add' 100 200).toNat                                    = (100 + 200 : UInt32).toNat
#guard (FBitVec32.add' (ofNat32 (2^31)) (ofNat32 (2^31))).toNat          = (2^31 + 2^31 : UInt32).toNat
#guard (FBitVec32.add' (ofNat32 (2^32 - 1)) 1).toNat                     = (2^32 - 1 + 1 : UInt32).toNat
#guard (FBitVec32.add' (ofNat32 (2^32 - 1)) (ofNat32 (2^32 - 1))).toNat  = (2^32 - 1 + 2^32 - 1 : UInt32).toNat
#guard (FBitVec32.add' 123456789 987654321).toNat                        = (123456789 + 987654321 : UInt32).toNat
#guard (FBitVec32.add' (ofNat32 (2^31 - 1)) 1).toNat                     = (2^31 - 1 + 1 : UInt32).toNat
#guard (FBitVec32.add' (ofNat32 (2^16)) (ofNat32 (2^16))).toNat          = (2^16 + 2^16 : UInt32).toNat
#guard (FBitVec32.add' 852 147).toNat                                    = (852 + 147 : UInt32).toNat
#guard (FBitVec32.add' 3000000000 2000000000).toNat                      = (3000000000 + 2000000000 : UInt32).toNat
#guard (FBitVec32.add' 112233 445566).toNat                              = (112233 + 445566 : UInt32).toNat
#guard (FBitVec32.add' 4294967290 10).toNat                              = (4294967290 + 10 : UInt32).toNat
#guard (FBitVec32.add' 123123 321321).toNat                              = (123123 + 321321 : UInt32).toNat

#guard (FBitVec32.sub' 30 30).toNat                                      = (30 - 30 : UInt32).toNat
#guard (FBitVec32.sub' 0 0).toNat                                        = (0 - 0 : UInt32).toNat
#guard (FBitVec32.sub' 1 0).toNat                                        = (1 - 0 : UInt32).toNat
#guard (FBitVec32.sub' 0 1).toNat                                        = (2^32 - 1 : UInt32).toNat
#guard (FBitVec32.sub' 1 2).toNat                                        = (2^32 - 1 : UInt32).toNat
#guard (FBitVec32.sub' 10 20).toNat                                      = (2^32 - 10 : UInt32).toNat
#guard (FBitVec32.sub' (ofNat32 (2^32 - 1)) 1).toNat                     = (2^32 - 1 - 1 : UInt32).toNat
#guard (FBitVec32.sub' (ofNat32 (2^32 - 1)) (ofNat32 (2^32 - 1))).toNat  = (2^32 - 1 - (2^32 - 1) : UInt32).toNat
#guard (FBitVec32.sub' 100 50).toNat                                     = (100 - 50 : UInt32).toNat
#guard (FBitVec32.sub' (ofNat32 (2^31 + 100)) (ofNat32 (2^31))).toNat    = (2^31 + 100 - 2^31 : UInt32).toNat
#guard (FBitVec32.sub' (ofNat32 (2^10)) 1).toNat                         = (1024 - 1 : UInt32).toNat
#guard (FBitVec32.sub' 0 (ofNat32 (2^32 - 1))).toNat                     = (0 - (2^32 - 1) : UInt32).toNat
#guard (FBitVec32.sub' (ofNat32 2863311530) (ofNat32 1431655765)).toNat  = (2863311530 - 1431655765 : UInt32).toNat
#guard (FBitVec32.sub' 500 100).toNat                                    = (500 - 100 : UInt32).toNat
#guard (FBitVec32.sub' 123456 65432).toNat                               = (123456 - 65432 : UInt32).toNat

-- Multiplication tests
#guard (FBitVec32.mul' 1 1).toNat                                        = (1 * 1 : UInt32).toNat
#guard (FBitVec32.mul' 123 0).toNat                                      = (123 * 0 : UInt32).toNat
#guard (FBitVec32.mul' 123 2).toNat                                      = (123 * 2 : UInt32).toNat
#guard (FBitVec32.mul' 2 2).toNat                                        = (2 * 2 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 (2^32 - 1)) 1).toNat                     = (2^32 - 1 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 (2^32 - 1)) (ofNat32 (2^32 - 1))).toNat  = ((2^32 - 1) * (2^32 - 1) : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 (2^31)) 2).toNat                         = (2^31 * 2 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 (2^30)) 4).toNat                         = (2^30 * 4 : UInt32).toNat
#guard (FBitVec32.mul' 123 456).toNat                                    = (123 * 456 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 2863311530) (ofNat32 1431655765)).toNat  = (2863311530 * 1431655765 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 0xAAAAAAAA) (ofNat32 0x55555555)).toNat  = (0xAAAAAAAA * 0x55555555 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 (2^31 - 1)) 2).toNat                     = ((2^31 - 1) * 2 : UInt32).toNat
#guard (FBitVec32.mul' 3 5).toNat                                        = (3 * 5 : UInt32).toNat
#guard (FBitVec32.mul' (ofNat32 4000000000) (ofNat32 3000000000)).toNat  = (4000000000 * 3000000000 : UInt32).toNat
#guard (FBitVec32.mul' 100 100).toNat                                    = (100 * 100 : UInt32).toNat

-- Shift Right tests
#guard (FBitVec32.shr' (ofNat32 10) 0).toNat          = 10 >>> 0
#guard (FBitVec32.shr' (ofNat32 0) 5).toNat           = 0 >>> 5
#guard (FBitVec32.shr' (ofNat32 2) 1).toNat           = 2 >>> 1
#guard (FBitVec32.shr' (ofNat32 123) 32).toNat        = 123 >>> 32
#guard (FBitVec32.shr' (ofNat32 123) 33).toNat        = 123 >>> 33
#guard (FBitVec32.shr' (ofNat32 (2^32 - 1)) 1).toNat  = (2^32 - 1) >>> 1
#guard (FBitVec32.shr' (ofNat32 (2^32 - 1)) 31).toNat = (2^32 - 1) >>> 31
#guard (FBitVec32.shr' (ofNat32 0xAAAAAAAA) 1).toNat  = 0xAAAAAAAA >>> 1
#guard (FBitVec32.shr' (ofNat32 0x55555555) 1).toNat  = 0x55555555 >>> 1
#guard (FBitVec32.shr' (ofNat32 (2^32 - 1)) 32).toNat = (2^32 - 1) >>> 32
#guard (FBitVec32.shr' (ofNat32 (2^31)) 15).toNat     = (2^31) >>> 15
#guard (FBitVec32.shr' (ofNat32 123456) 3).toNat      = 123456 >>> 3
#guard (FBitVec32.shr' (ofNat32 100) 2).toNat         = 100 >>> 2
#guard (FBitVec32.shr' (ofNat32 (2^31)) 31).toNat     = 2^31 >>> 31
#guard (FBitVec32.shr' (ofNat32 (2^31)) 30).toNat     = 2^31 >>> 30

end Tests

section CIRCOMLibSHA256

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/ch.circom
def ch (a b c : FBitVec32 p) : FBitVec32 p := a * (b - c) + c

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/maj.circom
def maj (a b c : FBitVec32 p) : FBitVec32 p :=
  let mid := b * c
  a * (b + c - 2*mid) + mid

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/xor3.circom
def xor3 (a b c : FBitVec32 p) : FBitVec32 p :=
  let mid := b * c;
  a * (1 - 2*b - 2*c + 4*mid) + b + c - 2*mid

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/rotate.circom
-- ra will be known at compile time as well i when reducing it. So (i + ra) % 32 is known number.
def rotr (x : FBitVec32 p) (ra : ZMod p) : FBitVec32 p := do
  (FBitVec32.zero).mapIdx (fun i (_ : ZMod p) => x[(i + ra) % 32]!)

def sigmaConstants : Array (ZMod p) := #[7, 18, 3, 17, 19, 10]

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/sigma.circom
def sigma0 (x : FBitVec32 p) : FBitVec32 p :=
  let rota := rotr x sigmaConstants[0]!
  let rotb := rotr x sigmaConstants[1]!
  let shrc := rotr x sigmaConstants[2]!
  xor3 rota rotb shrc

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/sigma.circom
def sigma1 (x : FBitVec32 p) : FBitVec32 p :=
  let rota := rotr x sigmaConstants[3]!
  let rotb := rotr x sigmaConstants[4]!
  let shrc := x.shr (sigmaConstants (p := p))[5]!
  xor3 rota rotb shrc

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/sigmaplus.circom
def sum0 (a : FBitVec32 p) : FBitVec32 p :=
  let rota := rotr a sigmaConstants[0]!
  let rotb := rotr a sigmaConstants[1]!
  let rotc := rotr a sigmaConstants[2]!
  xor3 rota rotb rotc

-- https://github.com/iden3/circomlib/blob/v2.0.5/circuits/sha256/sigmaplus.circom
def sum1 (a : FBitVec32 p) : FBitVec32 p :=
  let rota := rotr a sigmaConstants[3]!
  let rotb := rotr a sigmaConstants[4]!
  let rotc := rotr a sigmaConstants[5]!
  xor3 rota rotb rotc

end CIRCOMLibSHA256

instance : Clap.Sha2.ShaU32 (FBitVec32 p) (FBitVec8 p) where
  sum_0 := sum0
  sum_1 := sum1
  sigma_0 := sigma0
  sigma_1 := sigma1
  to_nat_be := FBitVec32.ofAFBitVec8
  ch
  maj

end Clap.Sha2.Circom
