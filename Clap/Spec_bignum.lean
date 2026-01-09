import Clap.Spec

namespace Clap

namespace Bignum

variable {p : ℕ} [Fact (Nat.Prime p)]

-- TODO any nat should be forbidden or translated to ZMod p ?

def to_byte_seq_be_array (x:ZMod p) (len:Nat) : Array UInt8 :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:ZMod p) (len:Nat) : List UInt8 :=
      let d : Nat := x.val / (2^8)
      let r : Nat := x.val % (2^8)
      -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
      let r : UInt8 := UInt8.ofNat r -- does not wrap as r < 256
      if len=0 then [] else
      r::(aux d (len-1))

lemma h (x:ZMod p) (len:Nat) :
  Array.size (to_byte_seq_be_array x len) = len := sorry

def to_byte_seq_be_vector (x:ZMod p) (len:Nat) : Vector UInt8 len :=
  ⟨to_byte_seq_be_array x len, h x len⟩

def to_byte_seq_be_bytearray (x:ZMod p) (len:Nat) : ByteArray :=
  ByteArray.mk (to_byte_seq_be_array x len)

#guard
  let n : ZMod prime_babybear := 255 + 1
  to_byte_seq_be_array n 2 = #[1,0]

#guard
  let n : ZMod prime_babybear := 2^16 + 2
  to_byte_seq_be_array n 3 = #[1,0,2]

#guard
  let n : ZMod prime_babybear := 2^16 + 2
  to_byte_seq_be_array n 4 = #[0,1,0,2]

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/


def from_byte_seq_be (bs:Array UInt8) : ZMod p :=
  Array.foldl (fun acc b => acc * 256 + (b.toNat : ZMod p)) (0:ZMod p) bs

#guard from_byte_seq_be (p:=prime_babybear) #[1] = 1
#guard from_byte_seq_be (p:=prime_babybear) #[255,1] = 255*256+1

lemma roundrip1 (x:ZMod p) (len:ℕ) (h: len <= (Nat.log2 p) / 8):
  from_byte_seq_be (to_byte_seq_be_array x len) = x := sorry

lemma roundrip2 (bs:Array UInt8) (h: p > 256 ^ bs.size) :
  to_byte_seq_be_array (from_byte_seq_be (p:=p) bs) bs.size = bs := sorry


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
-- #guard mul (p:=prime_babybear) #[1,1] #[1,1] = to_byte_seq_be_array (p:=prime_babybear) ((256+1) * (256+1)) 2

end Bignum
