import Clap.Spec.Sha2.Basic

namespace Clap.Spec.Sha2.Cpu

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

instance : Coe USize UInt8 where
  coe u := UInt8.ofNat u.toNat

instance : Coe USize UInt32 where
  coe u := UInt32.ofNat u.toNat

-- ROTR n x = (x >> n) ∨ (x << w - n)
def rotR (n : USize) (x : UInt32) : UInt32 :=
  (x >>> (n:UInt32)) ||| (x <<< (32 - (n:UInt32)))

def shiftRight (n : USize) (x : UInt32) : UInt32 :=
  x >>> (n:UInt32)

abbrev t : Clap.Spec.Sha2.T := {US:=USize, U8:=UInt8, U32:=UInt32}

instance : Clap.Spec.Sha2.Sha t where
  xor3
  rotR
  shiftRight
  to_nat_be
  ch
  maj

end Clap.Spec.Sha2.Cpu
