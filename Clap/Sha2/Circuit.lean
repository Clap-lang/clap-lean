import Clap.Lang
import Clap.Sha2.Basic
import Clap.Sha2.Cpu
import Clap.Wheels

import Clap.Compiler.Basic

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
    let yz := share (y * z)
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
    let yz := share (y * z)
    x * (1 - 2 * y - 2 * z + 4 * yz) + y + z - 2 * yz)
  ((x.zip y).zip z)


-- ROTR n x = (x >> n) ∨ (x << w - n)
def rotR (n : ℕ) (x : F32 p) : F32 p :=
  let (l,r) := List.splitAt n x
  r++l


def shiftRight (n : ℕ) (x : F32 p) : F32 p :=
  let l := List.drop n x
  l ++ List.replicate n 0

abbrev t p [Core p] [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)] : Clap.Sha2.T := {
  N  := F   (p:=p),
  U8  := F8  (p:=p),
  U32 := F32 (p:=p)
}

/-
  These instances must be given explicitely to avoid that the typeclass
  resolution mixes F8 and F32, which are the same actual type (List F)
  but are encoded with a different number of bits, 32 instead of 8.
-/

-- instance i₁ : Coe (F p) (F32 p) where
--   coe := F32.ofF!

instance i₂ : Coe (F8 p) (F32 p) where
  coe := F32.ofF8

-- instance i₄ : Coe (F p) (F8 p) where
--   coe := F8.ofF!

def to_nat_be (bs:Array (F8 p)) : F32 p :=
  let litteEndian := bs.toList.reverse
  List.flatten litteEndian

def toString (w:ℕ) (f : FBitVec p) : String :=
  assert! (f.length = w)
  let n : F p := ((f:List (FB p)).foldl (fun (pow,sum) i => (pow * 2, sum + (i * pow))) (1,0)).2
  let s := Core.onlyForDebugF.toString n
  if f.length != w then "ER" else s

instance (priority := high) i₇ : ToString (F32 p) where
  toString f := toString 32 f

instance (priority := high) i₈ : ToString (F8 p) where
  toString f := toString 8 f

-- instance : Clap.Sha2.Sha (t p) where
--   xor3
--   rotR
--   shiftRight
--   ch
--   maj
--   to_nat_be
--   i₁
--   i₂
--   i₄
--   i₇
--   i₈

end Clap.Sha2.Circuit


namespace Tests

abbrev p := Primes.goldilocks

open Clap.Sha2.Circuit
open Clap.Lang Core ZMod

instance : Coe ℕ (F p) where
  coe n := n

instance : Coe UInt8 (F8 p) where
  coe n := Clap.num2bitsLsbPure 8 n.toNat

instance (n:ℕ) : OfNat (F32 p) n where
  ofNat := Clap.num2bitsLsbPure 32 n

instance : Coe UInt32 (F32 p) where
  coe n := Clap.num2bitsLsbPure 32 n.toNat

example : ch (23 : F32 p) 45 56 = Clap.Sha2.Cpu.ch 23 45 56 := by native_decide
example : ch (12 : F32 p) 465 678 = Clap.Sha2.Cpu.ch 12 465 678 := by native_decide

example : maj (23 : F32 p) 45 56 = Clap.Sha2.Cpu.maj 23 45 56 := by native_decide
example : maj (12 : F32 p) 465 678 = Clap.Sha2.Cpu.maj 12 465 678 := by native_decide

example : xor3 (23 : F32 p) 45 56 = Clap.Sha2.Cpu.xor3 23 45 56 := by native_decide
example : xor3 (12 : F32 p) 465 678 = Clap.Sha2.Cpu.xor3 12 465 678 := by native_decide

example :
  letI n : ℕ := 3
  letI ins : UInt32 := 56
  rotR (p:=p) n (ins : F32 p) = Clap.Sha2.Cpu.rotR n ins := by native_decide

example :
  letI n : ℕ := 3
  letI ins : UInt32 := 56
  shiftRight (p:=p) n (ins : F32 p) = Clap.Sha2.Cpu.shiftRight n ins := by native_decide

example :
  letI ins : Array UInt8 := #[3,5,7,9]
  to_nat_be (p:=p) (ins.map fun (u8:UInt8) => (u8:F8 p)) = Clap.Sha2.Cpu.to_nat_be ins := by native_decide

namespace TestCompilation

def test₁ {p:ℕ} [Core p] [Fact (Primes.fits p 32)]
  (x y z : Vector (FB p) 32) : Option Unit := do
  let x : F32 p := x.toList
  let y : F32 p := y.toList
  let z : F32 p := z.toList
  F32.assert_eq (Clap.Sha2.Circuit.ch x y z) F32.default
  -- accept p
  
-- set_option trace.Clap.Compiler.reduce.trace true
/--
info: Compiled test₁ into test₁_circuit.
---
info: Wg for test₁ is test₁_wg_wrap.
-/
#guard_msgs in
#compile test₁ using Primes.goldilocks

end TestCompilation

end Tests
