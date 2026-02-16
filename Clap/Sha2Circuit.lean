import Clap.Lang
import Clap.Sha2
import Clap.Sha2Cpu
import Clap.Wheels

namespace Clap.Sha2.Circuit

open Clap.Lang

variable {p : ℕ} [Core p] [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)]

open Core

/-
Ch(x, y, z) =
 (x && y) XOR ( !x && z)  using arithmetic notation
  x * y - (not x) * z     using not x ~ x XOR true ~ x - 1
  x * y - (x - 1) * z
  x * y - x * z + z
  x * (y - z) + z         Circom format

000 0
001 1
010 0
011 1
100 0
101 0
110 1
111 1
-/

def ch (x y z : F32 p) : F32 p :=
  List.map (fun ((x,y),z) => x * (y - z) + z) ((x.zip y).zip z)

/-
Maj(x, y, z) =
  (x && y) XOR (x && z) XOR (y && z)
   x&y ^ x&z ^ y&z
   x*y + x*z + y*z - 2*x*y*z
   x*(y + z - 2*y*z) + y*z
which can be split into Circom format
yz = y*z
out = x*(y + z - 2*yz) + yz
-/
def maj (x y z : F32 p) : F32 p :=
  List.map (fun ((x,y),z) =>
    let yz := shareB (y * z)
    x * (y + z - 2 * yz) + yz)
  ((x.zip y).zip z)

/- Xor3
  x ^ y ^ z
  x - y - z
  x + y + z - 2*x*y - 2*x*z - 2*y*z + 4*x*y*z
  x * (1 - 2*y - 2*z + 4*y*z ) + y + z - 2*y*z
which can be split into Circom format
yz = y*z
out = x * (1 - 2*y - 2*z + 4*yz) + y + z - 2 * yz
-/
def xor3 (x y z : F32 p) : F32 p :=
  List.map (fun ((x,y),z) =>
    let yz := shareB (y * z)
    x * (1 - 2 * y - 2 * z + 4 * yz) + y + z - 2 * yz)
  ((x.zip y).zip z)


-- ROTR n x = (x >> n) ∨ (x << w - n)
def rotR (n : USize) (x : F32 p) : F32 p :=
  let (l,r) := List.splitAt n.toNat x
  r++l


def shiftRight (n : USize) (x : F32 p) : F32 p :=
  let l := List.drop n.toNat x
  l ++ List.replicate n.toNat 0

abbrev t p [Core p] [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)] : Clap.Sha2.T := {
  US:=F (p:=p),
  U8:=F8 (p:=p),
  U32:=F32 (p:=p)
}

instance : Coe (F p) (F8 p) where
  coe := F8.ofF

instance : Coe (F p) (F32 p) where
  coe := F32.ofF

instance : Coe (F8 p) (F32 p) where
  coe := F32.ofF8

def to_nat_be (bs:Array (F8 p)) : F32 p :=
  let litteEndian := bs.toList.reverse
  List.flatten litteEndian

instance : Clap.Sha2.Sha (t p) where
  xor3
  rotR
  shiftRight
  ch
  maj
  to_nat_be

end Clap.Sha2.Circuit


namespace Tests

abbrev p := Primes.goldilocks

open Clap.Sha2.Circuit
open Clap.Lang Core ZMod

instance : Coe ℕ (List (ZMod p)) where
  coe n := Clap.num2bitsLsbPure (p:=p) 32 (n:ZMod p)

def testCh (x y z expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (ch x y z) expected

example : testCh 23 45 56 45 = some () := by native_decide
example : (Clap.Sha2.Cpu.ch 23 45 56 = 45) := by native_decide

example : testCh 12 465 678 674 = some () := by native_decide
example : (Clap.Sha2.Cpu.ch 12 465 678 = 674) := by native_decide

def testMaj (x y z expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (maj x y z) expected

example : testMaj 23 45 56 61 = some () := by native_decide
example : (Clap.Sha2.Cpu.maj 23 45 56 = 61) := by native_decide

example : testMaj 12 465 678 132 = some () := by native_decide
example : (Clap.Sha2.Cpu.maj 12 465 678 = 132) := by native_decide

def testXor3 (x y z expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (xor3 x y z) expected

example : testXor3 23 45 56 2 = some () := by native_decide
example : (Clap.Sha2.Cpu.xor3 23 45 56 = 2) := by native_decide

example : testXor3 12 465 678 891 = some () := by native_decide
example : (Clap.Sha2.Cpu.xor3 12 465 678 = 891) := by native_decide

def testRotR (n:USize) (x expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (rotR n x) expected

example : testRotR 3 56 7 = some () := by native_decide
example : (Clap.Sha2.Cpu.rotR 3 56 = 7) := by native_decide

def testShiftRight (n:USize) (x expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (shiftRight n x) expected

example : testShiftRight 3 56 7 = some () := by native_decide
example : (Clap.Sha2.Cpu.shiftRight 3 56 = 7) := by native_decide

def testToNatBe (bs: Array (List (ZMod p))) (expected : ZMod p) : Option Unit :=
  F32.assert_eq (p := p) (to_nat_be bs) expected

#guard (Clap.Sha2.Cpu.to_nat_be #[3,5,7] = 197895)
#guard! testToNatBe (#[3,5,7].map (fun (x:ℕ) => (x:List (ZMod p)))) 197895 = some ()

end Tests
