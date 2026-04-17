import Clap.Wheels
import Clap.Sha2.Basic

namespace Clap.Sha2.Cpu

instance : Coe UInt8 UInt32 where
  coe u8 := UInt32.ofNat u8.toNat

def to_nat_be (bs:Array UInt8) : UInt32 :=
  Array.foldl (fun acc (b:UInt8) => acc * 256 + (b:UInt32)) (0:UInt32) bs

-- Ch(x, y, z) = (x && y) XOR ( !x && z)
def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

-- Maj(x, y, z) = (x && y) XOR (x && z) XOR (y && z)
def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def xor3 (x y z : UInt32) : UInt32 :=
  x ^^^ y ^^^ z

/- Section 4.1.2
     use six logical functions, where each function operates on 32-bit words,
     which are represented as x, y, and z. The result of each function is a
     new 32-bit word. For SHA-512, 64-bit operations are used.
-/

instance : Coe ℕ UInt8 where
  coe := UInt8.ofNat

instance : Coe ℕ UInt32 where
  coe := UInt32.ofNat

-- ROTR n x = (x >> n) ∨ (x << w - n)
def rotR (n : ℕ) (x : UInt32) : UInt32 :=
  (x >>> (n:UInt32)) ||| (x <<< (32 - (n:UInt32)))

def shiftRight (n : ℕ) (x : UInt32) : UInt32 :=
  x >>> (n:UInt32)

abbrev t : Clap.Sha2.T := {U8:=UInt8, U32:=UInt32}

instance (priority := high) i₆ : ToString UInt32 where
  toString f := Clap.natToHex f.toNat

instance : Clap.Sha2.Sha t where
  rotR
  shiftRight
  to_nat_be
  ch
  i₆

instance : Clap.Sha2.U32Monadic Id UInt32 where
  add32 := UInt32.add
  xor3
  maj

end Clap.Sha2.Cpu
