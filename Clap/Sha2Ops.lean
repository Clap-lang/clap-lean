import Clap.Sha2

namespace Clap.Sha2_ops

variable {U8 : Type}
  [Coe UInt8 U8]

def of_nat_be (x:Nat) (len:Nat) : Array U8 :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:Nat) (len:Nat) : List U8 :=
      let d : Nat := x / (2^8)
      let r : Nat := x % (2^8)
      let r : U8 := UInt8.ofNat r -- does not wrap as r < 256
      if len=0 then [] else
      r::(aux d (len-1))

def stringToU8s (s:String) : Array U8 :=
  let bs : ByteArray := s.toUTF8
  let bs : Array UInt8 := bs.data
  bs.map (fun (b:UInt8) => (b:U8))

instance : Clap.Sha2.ShaU8 U8 where
  of_nat_be
  stringToU8s


variable {U32 : Type}
  [∀ (n:Nat), OfNat U32 n]
  [Coe U8 U32]
  [HAnd U32 U32 U32] -- [And U32] ?
  [HXor U32 U32 U32] -- [Xor U32] ?
  [Complement U32]
  [HShiftLeft U32 U32 U32] -- [ShiftLeft U32] ?
  [HShiftRight U32 U32 U32] -- [ShiftRight U32] ?
  [HOr U32 U32 U32]
  [HAdd U32 U32 U32]
  [HSub U32 U32 U32]
  [HMul U32 U32 U32]
  [Inhabited U32]

def to_nat_be (bs:Array U8) : U32 :=
  Array.foldl (fun acc (b:U8) => acc * 256 + (b:U32)) (0:U32) bs

-- Ch(x, y, z) = (x && y) XOR ( !x && z)
def ch (x y z : U32) : U32 :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

-- Maj(x, y, z) = (x && y) XOR (x && z) XOR (y && z)
def maj (x y z : U32) : U32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/- Section 4.1.2
     use six logical functions, where each function operates on 32-bit words,
     which are represented as x, y, and z. The result of each function is a
     new 32-bit word. For SHA-512, 64-bit operations are used.
-/

-- ROTR n x = (x >> n) ∨ (x << w - n)
def rotR (n x : U32) : U32 :=
  (x >>> n) ||| (x <<< (32 - n))

def sum_constants : Array U32 := #[2, 13, 22, 6, 11, 25]

-- Sum_0(x) = ROTR^{c0}(x) XOR ROTR^{c1}(x) XOR ROTR^{c2}(x)
def sum_0 (x : U32) : U32 :=
  (rotR (sum_constants[0]!)) x ^^^
  (rotR (sum_constants[1]!)) x ^^^
  (rotR (sum_constants[2]!)) x

-- Sum_1(x) = ROTR^{c3}(x) XOR ROTR^{c4}(x) XOR ROTR^{c5}(x)
def sum_1 (x : U32) : U32 :=
  (rotR sum_constants[3]!) x ^^^
  (rotR sum_constants[4]!) x ^^^
  (rotR sum_constants[5]!) x

def sigma (c0 c1 c2 x : U32) : U32 :=
  (rotR c0 x) ^^^ (rotR c1 x) ^^^ (x >>> c2)

instance : Clap.Sha2.ShaU32 U32 U8 where
  sum_0
  sum_1
  sigma
  to_nat_be
  ch
  maj

end Clap.Sha2_ops
