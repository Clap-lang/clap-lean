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

lemma ZMod_add_no_overflow3 {p:ℕ} (a b c : ZMod p) (h : a.val + b.val + c.val < p) :
  (a + b + c).val = a.val + b.val + c.val := by sorry

variable {p : ℕ}
variable [Fact (Nat.Prime p)]

abbrev FB p := ZMod p

namespace FB

def isValid (x:FB p) : Prop := x.val < 2

def Valid : Type := {x:FB p // x.isValid }

instance : CoeOut (FB p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FB p) where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

def true (h:p≠1): @Valid p := ⟨1, by simp [isValid]; rw [ZMod.val_one''] ; simp ; assumption⟩
def false : @Valid p := ⟨0, by simp [isValid]⟩

end FB

abbrev FU8 p := ZMod p

namespace FU8

def isValid (x:FU8 p) : Prop := x.val < 256

def Valid : Type := {x:FU8 p // x.isValid }

instance : CoeOut (FU8 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FU8 p) where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

def mk (x:FU8 p) : Option Unit := Spec.assert_range 8 x

def mk_some (x:FU8 p) (h:x.val<256) : x.mk = some () := by simp [mk,Spec.assert_range]; assumption

def add (a b : FU8 p) : Option (FU8 p) := do
  let o := a + b
  Spec.assert_range 8 o
  o

def add_spec (a b : FU8 p) :
  (a.val + b.val < 256) ->
  (add a b = some (a.val + b.val)) := sorry

def add_sound (a b o : FU8 p) :
  (add a b = some o) ->
  (o = a.val + b.val) ∧ isValid o ∧ isValid a ∧ isValid b := sorry

end FU8

/-
  FU8.add is annoying to work with because it return Option
  We want to replace it with ZMod.add which is always defined and easier to work with.
  We show a refinement between the two.
-/

def ex_low (a b o : ZMod p) : Option Unit := do
  let o' <- FU8.add a b
  Spec.eq0 (o - o')
  Spec.accept ()

def ex_high (a b o : FU8 p) : Option Unit := do
  let o' := a + b
  Spec.eq0 (o - o')
  Spec.accept ()

def ex_high_refines_low : Simulation.r_sim (F:=(ZMod p)) ex_high (ex_low (p:=p)) := by
  unfold ex_high ex_low FU8.add Spec.assert_range
  repeat (
    apply Simulation.r_sim.lam
    intro)
  simp
  split
  . constructor
  . apply Simulation.r_sim.right_none

/-
  we could also have a completeness theorem that states that if the inputs to high respect some bounds then low will always return some
-/

lemma div_rem_spec (a:ZMod p) :
  letI o := Spec.div_rem a
  a.val = o.1 * 256 + o.2 := by
  simp [Spec.div_rem]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  rw [Nat.div_mod_eq_div]
  omega
  repeat apply ZMod.val_lt

lemma div_rem_spec_valid (a:ZMod p) :
  letI o := Spec.div_rem a
  FU8.isValid o.2 := by
  simp [Spec.div_rem]
  simp [FU8.isValid]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  omega
  apply ZMod.val_lt

namespace ByteArray

-- TODO actually convert to/from ByteArray instead of Array UInt8

def of_nat_be (x:ℕ) (len:Nat) : Array (FU8 p) :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:ℕ) (len:Nat) : List (FU8 p) :=
      let d : ℕ := x / (2^8)
      let r : ℕ := x % (2^8)
      -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
      let r : FU8 p := r -- does not wrap as r < 256
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
  of_nat_be (p:=prime_babybear) n 2 = #[1,0]
#guard
  let n : ℕ := 2^16 + 2
  of_nat_be (p:=prime_babybear) n 3 = #[1,0,2]
#guard
  let n : ℕ := 2^16 + 2
  of_nat_be (p:=prime_babybear) n 4 = #[0,1,0,2]

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/

def to_nat_be (bs:Array (FU8 p)) : ℕ :=
  Array.foldl (fun acc (b:ZMod p) => acc * 256 + (b:ℕ)) (0:ℕ) bs

#guard to_nat_be (p:=prime_babybear) #[1] = 1
#guard to_nat_be (p:=prime_babybear) #[255,1] = 255*256+1

def min_bits (x:ℕ) : ℕ :=
  let n_bits := Nat.log2 x
  if 2^n_bits < x then n_bits+1 else n_bits

def min_bytes (x:ℕ) : ℕ :=
  let n_bits := min_bits x
  if n_bits % 8 = 0 then n_bits / 8 else (n_bits / 8) + 1

lemma roundrip1 (x:ℕ) (len:ℕ) (h: len <= min_bytes x) :
  to_nat_be (of_nat_be (p:=p) x len) = x := sorry

#guard
  let n : ℕ := 255 + 1
  to_nat_be (of_nat_be (p:=prime_babybear) n 2) = n
#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be (p:=prime_babybear) n 3) = n
#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be (p:=prime_babybear) n 4) = n

lemma roundrip2 (bs:Array (FU8 p)) :
  of_nat_be (to_nat_be bs) bs.size = bs := sorry

#guard of_nat_be (p:=prime_babybear) (to_nat_be (p:=prime_babybear) #[1]) 1 = #[1]
#guard of_nat_be (p:=prime_babybear) (to_nat_be  (p:=prime_babybear) #[255,1]) 2 = #[255,1]

end ByteArray

namespace Bignum

def add_carry (a b : FU8 p) (c : FB p :=0) : FU8 p × FB p :=
  -- behaves well only if p>2^(8+1+1)
  let o : FU8 p := a + b + c
  let (d,r) := Spec.div_rem o
  (r,d)

lemma add_carry_spec (a b :@FU8.Valid p) (c:@FB.Valid p := FB.false)
  (hp: 256+256+2<p) :
  letI o : FU8 p × FB p := add_carry (a:FU8 p) (b:FU8 p) (c:FB p)
  (a:ℕ)+(b:ℕ)+(c:ℕ) = (o.2:ℕ) * 256 + (o.1:ℕ)
  := by
  have hab: ZMod.val a.val + ZMod.val b.val < 256+256 := by
    apply Nat.add_lt_add
    apply a.prop
    apply b.prop
  let drs := div_rem_spec ((a:FU8 p)+(b:FU8 p)+(c:FU8 p))
  simp at drs
  simp [add_carry]
  rw [<-drs]
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

lemma Nat.add_lt_add3 (a b c ta tb tc : ℕ) (ha: a<ta) (hb:b<tb) (hc:c<tc) : a + b + c < ta + tb + tc := by
  apply Nat.add_lt_add
  apply Nat.add_lt_add
  repeat assumption

lemma add_carry_spec_valid (a b :@FU8.Valid p) (c:@FB.Valid p := FB.false)
  (hp: 256+256+2<p) :
  letI o := add_carry a (b) (c:FB p)
  FU8.isValid o.1 ∧ FB.isValid o.2
  := by
  constructor
  apply div_rem_spec_valid

  simp [add_carry,FB.isValid,Spec.div_rem]
  --  rw [Nat.div_mod_eq_div]
  --  rw [ZMod_add_no_overflow3]
  --  apply Nat.div_lt_of_lt_mul
  --  rw [Nat.add_div_eq_of_add_mod_lt
  --  apply Nat.add_lt_add3 (b:=256)
  -- apply lt_trans (b:=256+256+2)
  -- apply a.prop
  -- omega
  sorry


#guard add_carry (p:=prime_babybear) 1 1 = (2,0)
#guard add_carry (p:=prime_babybear) 255 2 = (1,1)
#guard add_carry (p:=prime_babybear) 255 3 = (2,1)
#guard add_carry (p:=prime_babybear) 255 255 1 = (255,1)
#guard add_carry (p:=prime_babybear) 300 300 5 = (93,2) -- nonsense

open Spec in
def ex (a b : FU8 p) : Option Unit := do
  FU8.mk a
  FU8.mk b
  let (_o,c') := add_carry a b
  eq0 c'
  accept ()

-- set_option pp.parens true in
-- lemma ex_spec (hp:514<p) (a b : FU8 p)
--   (hex: ex a b = some () <-> precondition) : FU8.isValid a := by
--   simp [ex,Option.bind,Spec.eq0] at hex
--   have h: _ := add_carry_spec (p:=p) ⟨a,?av⟩ ⟨b,?bv⟩ --⟨0,?cv⟩
--   simp at h
--   apply h at hp
--   rcases hp with ⟨h1,h2,h3⟩
--   repeat (rw [FU8.mk_some] at * ; simp at *)
--   have hfalse: (FB.false : @FB.Valid p).val = 0 := sorry
--   rw [hfalse] at h1
--   repeat sorry
--   -- rw [<-ZMod_add_no_overflow (a:=(add_carry a b).2 * 256) (b:=(add_carry a b).1)] at h1
--   -- rw [<-h1] at hex
--   -- -- rcases h with gh
--   -- -- split
--   -- -- apply ZMod.val_lt

def add (a b:Array (FU8 p)) : Array (FU8 p) :=
  let abs := Array.zip a b -- assume a b of same length, they not need to be
  let (c,res) : ZMod p × Array (FU8 p) :=
    Array.foldl (fun (c,res) (a,b) ↦
      let (ab,c) := add_carry a b c
      (c,Array.push res ab))
    (0,#[]) abs.reverse
  let res := if c ≠ 0 then Array.push res c.val else res
  Array.reverse res

#guard add (p:=prime_babybear) #[1] #[1] = #[2]
#guard add (p:=prime_babybear) #[0,1] #[0,1] = #[0,2]
#guard add (p:=prime_babybear) #[0,255] #[0,1] = #[1,0]
#guard add (p:=prime_babybear) #[0,255] #[0,255] = #[1,254]

open ByteArray in
def add_spec (a b len: ℕ)
  (h: min_bytes a = min_bytes b)
  (hlen: min_bytes a ≤ len) :
  add (p:=p) (of_nat_be a len) (of_nat_be b len) =
    of_nat_be (a + b) len
  := sorry

-- def add_spec (a b : Array (FU8 p)) len :
--   add a b = (ByteArray.of_nat_be ((ByteArray.to_nat_be a) + (ByteArray.to_nat_be b)) len) := by
--   simp [add]

def add_spec_valid (a b : Array (FU8 p)) :
  Array.all (add a b) (fun x ↦ x.val < 256) := sorry

def UInt8.mul_carry (a b : UInt8) (c : ZMod p :=0) : UInt8 × (ZMod p) :=
  let a : ZMod p := a.toNat
  let b : ZMod p := b.toNat
  let o : ZMod p := a * b + c -- 2*8+1 bits
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
