import Clap.Spec

namespace Clap

-- Auxiliary functions to go from/to ByteArrays to/from ℕ
namespace ByteArray

-- TODO actually convert to/from ByteArray instead of Array UInt8

-- hacspec: to_byte_seq_be_array
def of_nat_be (x:ℕ) (len:Nat) : Array UInt8 :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:ℕ) (len:Nat) : List UInt8 :=
      let d : Nat := x / (2^8)
      let r : Nat := x % (2^8)
      -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
      let r : UInt8 := UInt8.ofNat r -- does not wrap as r < 256
      if len=0 then [] else
      r::(aux d (len-1))

-- lemma h (x:ℕ) (len:Nat) :
--   Array.size (of_nat_be x len) = len := sorry

-- def of_nat_be_vector (x:ℕ) (len:Nat) : Vector UInt8 len :=
--   ⟨of_nat_be x len, h x len⟩

-- def of_nat_be_bytearray (x:ℕ) (len:Nat) : ByteArray :=
--   ByteArray.mk (of_nat_be x len)

#guard
  let n : ℕ := 255 + 1
  of_nat_be n 2 = #[1,0]

#guard
  let n : ℕ := 2^16 + 2
  of_nat_be n 3 = #[1,0,2]

#guard
  let n : ℕ := 2^16 + 2
  of_nat_be n 4 = #[0,1,0,2]

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/

def to_nat_be (bs:Array UInt8) : ℕ :=
  Array.foldl (fun acc b => acc * 256 + b.toNat) 0 bs

#guard to_nat_be #[1] = 1
#guard to_nat_be #[255,1] = 255*256+1

def min_bytes (x:ℕ) : ℕ :=
  let n_bits := Nat.log2 x
  let n_bits := if 2^n_bits < x then n_bits+1 else n_bits
  if n_bits % 8 = 0 then n_bits / 8 else (n_bits / 8) + 1

lemma roundrip1 (x:ℕ) (len:ℕ) (h: len <= min_bytes x) :
  to_nat_be (of_nat_be x len) = x := sorry

#guard
  let n : ℕ := 255 + 1
  to_nat_be (of_nat_be n 2) = n

#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be n 3) = n

#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be n 4) = n

lemma roundrip2 (bs:Array UInt8) :
  of_nat_be (to_nat_be bs) bs.size = bs := sorry

#guard of_nat_be (to_nat_be #[1]) 1 = #[1]
#guard of_nat_be (to_nat_be #[255,1]) 2 = #[255,1]

end ByteArray

namespace Bignum

variable {p : ℕ}
variable [Fact (Nat.Prime p)]

def UInt8.add_carry (a b : UInt8) (c : ZMod p :=0) : UInt8 × (ZMod p) :=
  let a : ZMod p := a.toNat
  let b : ZMod p := b.toNat
  let o : ZMod p := a+b+c -- 8+1 bit
  let (d,r) := Spec.div_rem o
  (UInt8.ofNat r.val,d)

#guard UInt8.add_carry (p:=prime_babybear) 1 1 = (2,0)
#guard UInt8.add_carry (p:=prime_babybear) 255 2 = (1,1)
#guard UInt8.add_carry (p:=prime_babybear) 255 3 = (2,1)

def add (a b:Array UInt8) : Array UInt8 :=
  let abs : Array (UInt8 × UInt8) := Array.zip a b
  let (c,res) : ZMod p × Array UInt8 :=
    Array.foldl (fun (c,res) (a,b) ↦
      let (ab,c) := UInt8.add_carry a b c
      (c,Array.push res ab))
    ((0,#[]) : ZMod p × Array UInt8) abs.reverse
  let res := if c ≠ 0 then Array.push res (UInt8.ofNat c.val) else res
  Array.reverse res

#guard add (p:=prime_babybear) #[1] #[1] = #[2]
#guard add (p:=prime_babybear) #[0,1] #[0,1] = #[0,2]
#guard add (p:=prime_babybear) #[0,255] #[0,1] = #[1,0]
#guard add (p:=prime_babybear) #[0,255] #[0,255] = #[1,254]

def UInt8.mul_carry (a b : UInt8) (c : ZMod p :=0) : UInt8 × (ZMod p) :=
  let a : ZMod p := a.toNat
  let b : ZMod p := b.toNat
  let o : ZMod p := a * b + c -- 2*8+1 bits?
  let (d,r) := Spec.div_rem o
  (UInt8.ofNat r.val,d)

#guard UInt8.mul_carry (p:=prime_babybear) 2 2 = (4,0)
#guard UInt8.mul_carry (p:=prime_babybear) 128 2 = (0,1)
#guard UInt8.mul_carry (p:=prime_babybear) 128 2 = (0,1)

def mul_one_line (a:Array UInt8) (b : UInt8) (c : ZMod p :=0) : Array UInt8 × ZMod p :=
    let (res,c) := aux a.reverse.toList c []
    (res.toArray,c)
  where
  aux (as:List UInt8) (c:ZMod p) (res:List UInt8) : List UInt8 × ZMod p :=
    match as with
    | [] => (res,c)
    | a::as =>
      let (ab,c) := UInt8.mul_carry a b c
      aux as c (ab::res)

#guard mul_one_line (p:=prime_babybear) #[1] 1 = (#[1],0)
#guard mul_one_line (p:=prime_babybear) #[0,1] 1 = (#[0,1],0)
#guard mul_one_line (p:=prime_babybear) #[0,2] 255 = (#[1,254],0)
#guard mul_one_line (p:=prime_babybear) #[1,2] 255 = (#[0,254],1)

-- TODO need to implement schoolbook multiplication
def mul (a b:Array UInt8) : Array UInt8 :=
  sorry

-- #guard mul (p:=prime_babybear) #[1] #[1] = #[1]
-- #guard mul (p:=prime_babybear) #[0,1] #[0,1] = #[0,1]
-- #guard mul (p:=prime_babybear) #[1,1] #[1,1] = ByteArray.of_nat_be ((256+1) * (256+1)) 2

end Bignum
