import Clap.Spec

namespace Clap

lemma ZMod_add_no_overflow {p:ℕ} (a b : ZMod p) (h : a.val + b.val < p) :
  (a + b).val = a.val + b.val := by
  rcases p with _|p
  grind
  simp [ZMod] at *
  simp [ZMod] at a b
  unfold ZMod.val
  dsimp
  unfold ZMod.val at h
  dsimp at h
  rcases a
  rcases b
  simp at *
  rw [Fin.add_def]
  simp
  assumption

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

def min_bits (x:ℕ) : ℕ :=
  let n_bits := Nat.log2 x
  if 2^n_bits < x then n_bits+1 else n_bits

def min_bytes (x:ℕ) : ℕ :=
  let n_bits := min_bits x
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


abbrev FB p := ZMod p

namespace FB

variable {p : ℕ}

def isValid (x:FB p) : Prop := x.val < 2

def Valid : Type := {x:FB p // x.isValid } -- TODO only for specs

instance : CoeOut (FB p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

def true (h:p≠1): @Valid p := ⟨1, by simp [isValid]; rw [ZMod.val_one''] ; simp ; assumption⟩
def false : @Valid p := ⟨0, by simp [isValid]⟩

end FB

abbrev FU8 p := ZMod p

namespace FU8

variable {p : ℕ}
variable [Fact (Nat.Prime p)]

def isValid (x:FU8 p) : Prop := x.val < 256

def Valid : Type := {x:FU8 p // x.isValid } -- TODO only for specs

instance : CoeOut (FU8 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

def add_carry (a b : FU8 p) (c : FB p :=0) : FU8 p × FB p :=
  -- behaves well only of p>2^(8+1+1)
  let o : FU8 p := a + b + c
  let (d,r) := Spec.div_rem o
  (r,d)

lemma div_rem_spec (a:ZMod p) :
  let (d,r) := Spec.div_rem a
  a.val = d.val * 256 + r.val ∧ FU8.isValid r := by
  simp [Spec.div_rem]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  rw [Nat.div_mod_eq_div]
  constructor
  omega
  apply ZMod.val_lt at a
  simp [FU8.isValid]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  omega
  repeat apply ZMod.val_lt

lemma add_carry_spec (a b :@Valid p) (c:@FB.Valid p)
  (hp: 256+256+2<p) :
  let (o,c') : FU8 p × FB p := add_carry (a:FU8 p) (b:FU8 p) (c:FB p)
  (a:ℕ)+(b:ℕ)+(c:ℕ) = (c':ℕ) * 256 + (o:ℕ)
  ∧ FU8.isValid o ∧ FB.isValid c'
  := by
  have hab: ZMod.val a.val + ZMod.val b.val < 256+256 := by
    apply Nat.add_lt_add
    apply a.prop
    apply b.prop
  let drs := div_rem_spec ((a:FU8 p)+(b:FU8 p)+(c:FU8 p))
  simp at drs
  rcases drs with ⟨hl, hr⟩
  simp [add_carry]
  constructor
  rw [<-hl]
  rw [ZMod_add_no_overflow]
  rw [ZMod_add_no_overflow]
  apply lt_trans
  apply hab
  apply lt_trans (b:=256+256+2)
  omega
  apply hp
  have hc: ZMod.val (a.val+b.val) + ZMod.val c.val < (256+256+2) := by
    apply Nat.add_lt_add
    rw [ZMod_add_no_overflow]
    apply Nat.add_lt_add
    apply a.prop
    apply b.prop
    apply lt_trans
    apply hab
    apply lt_trans (b:=256+256+2)
    omega
    apply hp
    apply c.prop
  apply lt_trans
  apply hc
  apply hp
  constructor
  apply hr
  simp [FB.isValid, Spec.div_rem]
  sorry
--  rw [Nat.div_mod_eq_div]


#guard add_carry (p:=prime_babybear) 1 1 = (2,0)
#guard add_carry (p:=prime_babybear) 255 2 = (1,1)
#guard add_carry (p:=prime_babybear) 255 3 = (2,1)
#guard add_carry (p:=prime_babybear) 255 255 1 = (255,1)
#guard add_carry (p:=prime_babybear) 300 300 5 = (93,2) -- nonsense

end FU8

namespace Bignum

variable {p : ℕ}

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
