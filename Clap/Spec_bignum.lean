import Clap.Spec

namespace Clap

section Wheels

lemma ZMod_add_no_overflow {p : ℕ} (a b : ZMod p) (h : a.val + b.val < p) :
  (a + b).val = a.val + b.val :=
by
  rcases p with _ | p
  · grind
  · simp [ZMod] at *; simp [ZMod] at a b
    unfold ZMod.val at *; dsimp at *
    rcases a; rcases b; simp at *
    rw [Fin.add_def]; simp
    assumption

end Wheels

variable {p : ℕ}
variable [Fact (Nat.Prime p)]

abbrev FB p := ZMod p

namespace FB

def isValid (x : FB p) : Prop := x.val < 2

def Valid : Type := {x : FB p // x.isValid } -- TODO only for specs

instance : CoeOut (FB p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FB p) where
  coe x := x.val

def true (h : p ≠ 1): @Valid p :=
  ⟨1, by simp [isValid]; rw [ZMod.val_one'']; simp; assumption⟩

def false : @Valid p :=
  ⟨0, by simp [isValid]⟩

end FB

abbrev FU8 p := ZMod p

instance : ToString (FU8 p) where
  toString a := a.val

namespace FU8

def isValid (x : FU8 p) : Prop := x.val < 2^8

def Valid : Type := {x : FU8 p // x.isValid } -- TODO only for specs

instance : CoeOut (FU8 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FU8 p) where
  coe x := x.val

-- def addCarry (a b : FU8 p) (c : FB p := 0) : FU8 p × FB p :=
--   -- behaves well only if p>2^(8+1+1)
--   Spec.div_rem (a + b + c) |>.swap

-- --attribute [instance high] instCoeOutValid
-- example (a b : @FU8.Valid p) (c : @FB.Valid p) :
--   addCarry a b c.val = (1,1) := sorry

def mk (x : FU8 p) : Option Unit := Spec.assert_range 8 x

omit [Fact (Nat.Prime p)] in
lemma mk_some (x : FU8 p) (h : x.val < 2^8) : x.mk = some () := by
  simp [mk, Spec.assert_range]; assumption

end FU8

lemma div_rem_spec (a : ZMod p) :
  letI o := Spec.div_rem a
  a.val = o.1 * 2^8 + o.2 :=
by
  simp [Spec.div_rem]
  rw [Nat.mod_mod_eq_mod_of_lt_right, Nat.div_mod_eq_div]
  · omega
  · apply ZMod.val_lt
  · apply ZMod.val_lt

lemma div_rem_spec_valid (a : ZMod p) :
  FU8.isValid (Spec.div_rem a).2 :=
by
  simp [Spec.div_rem, FU8.isValid]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  · omega
  · apply ZMod.val_lt

namespace ByteArray

lemma uint8_valid (a : UInt8) (h : 2^8 ≤ p) : @FU8.isValid p a.toNat := by
  simp [FU8.isValid]
  have : a.toNat < 2^8 := by apply UInt8.toNat_lt
  rw [Nat.mod_eq_of_lt]
  · assumption
  · omega

instance : CoeOut (@FU8.Valid p) UInt8 where
  coe x := UInt8.ofNatLT x.val (by exact x.property)

instance : CoeOut (FU8 p) UInt8 where
  coe x := UInt8.ofNat x.val

instance : Coe UInt8 (FU8 p) where
  coe x := x.toNat

instance {h : 2^8 ≤ p} : Coe UInt8 (@FU8.Valid p) where
  coe x := ⟨x.toNat, by apply uint8_valid; assumption⟩

-- TODO actually convert to/from ByteArray instead of Array UInt8
/- Little endian -/
def ofNat (x len : ℕ) : ByteArray := ⟨aux x len⟩
where
  aux (x len : ℕ) : Array UInt8 :=
    let d : ℕ := x / 2^8
    let r : ℕ := x % 2^8
    if len = 0 then #[] else ⟨(UInt8.ofNatLT r (by grind)) :: (aux d (len - 1)).toList⟩

@[reducible]
def ofFU8 (x : FU8 p) (len : ℕ) : ByteArray :=
  ofNat x len

-- def of_nat_be (x:ℕ) (len:Nat) : Array (FU8 p) :=
--     (List.reverse (aux x len)).toArray
--   where
--     aux (x:ℕ) (len:Nat) : List (FU8 p) :=
--       let d : ℕ := x / (2^8)
--       let r : ℕ := x % (2^8)
--       -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
--       let r : FU8 p := r -- does not wrap as r < 256
--       if len=0 then [] else
--       r::(aux d (len-1))

-- #guard
--   let n : ℕ := 255 + 1
--   of_nat_be (p:=prime_babybear) n 2 = #[1,0]
-- #guard
--   let n : ℕ := 2^16 + 2
--   of_nat_be (p:=prime_babybear) n 3 = #[1,0,2]
-- #guard
--   let n : ℕ := 2^16 + 2
--   of_nat_be (p:=prime_babybear) n 4 = #[0,1,0,2]

#guard (ofNat (255 + 1)  2 |>.data) = #[0,1]
#guard (ofNat (2^16 + 2) 3 |>.data) = #[2,0,1]
#guard (ofNat (2^16 + 2) 4 |>.data) = #[2,0,1,0]
#guard (ofFU8 (255 + 1  : FU8 prime_babybear) 2 |>.data) = #[0,1]
#guard (ofFU8 (2^16 + 2 : FU8 prime_babybear) 3 |>.data) = #[2,0,1]
#guard (ofFU8 (2^16 + 2 : FU8 prime_babybear) 4 |>.data) = #[2,0,1,0]

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/

def toNat (bs : ByteArray) : ℕ :=
  bs.data.foldr (fun (b : UInt8) acc => acc * 2^8 + b.toNat) 0

@[reducible]
def toFU8 (bs : ByteArray) : FU8 p := toNat bs

#guard toNat ⟨#[1]⟩ = 1
#guard toNat ⟨#[1,255]⟩ = 255*256+1
#guard toNat ⟨#[1,2,3]⟩ = 3*256*256 + 2*256 + 1
#guard toNat ⟨#[2,0,1,0]⟩ = 65536 + 2

def to_nat_be (bs:Array (FU8 p)) : ℕ :=
  Array.foldl (fun acc (b:ZMod p) => acc * 256 + (b:ℕ)) (0:ℕ) bs

#guard to_nat_be (p:=prime_babybear) #[1] = 1
#guard to_nat_be (p:=prime_babybear) #[255,1] = 255*256+1
#guard to_nat_be (p:=prime_babybear) #[3,2,1] = 3*256*256 + 2*256 + 1

def minBits (x : ℕ) : ℕ :=
  let nb := Nat.log2 x
  if 2^nb < x then nb + 1 else nb

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

-- lemma roundrip1 (x:ℕ) (len:ℕ) (h: len <= min_bytes x) :
--   to_nat_be (of_nat_be (p:=p) x len) = x := sorry

#guard let n : ℕ := 255  + 1; toNat (ofNat n 2) = n
#guard let n : ℕ := 2^16 + 2; toNat (ofNat n 3) = n
#guard let n : ℕ := 2^16 + 2; toNat (ofNat n 4) = n

-- #guard
--   let n : ℕ := 255 + 1
--   to_nat_be (of_nat_be (p:=prime_babybear) n 2) = n
-- #guard
--   let n : ℕ := 2^16 + 2
--   to_nat_be (of_nat_be (p:=prime_babybear) n 3) = n
-- #guard
--   let n : ℕ := 2^16 + 2
--   to_nat_be (of_nat_be (p:=prime_babybear) n 4) = n

-- lemma roundrip2 (bs:Array (FU8 p)) :
--   of_nat_be (to_nat_be bs) bs.size = bs := sorry

#guard ofNat (toNat ⟨#[1]⟩) 1 = ⟨#[1]⟩
#guard ofNat (toNat ⟨#[1,255]⟩) 2 = ⟨#[1,255]⟩

-- #guard of_nat_be (p:=prime_babybear) (to_nat_be (p:=prime_babybear) #[1]) 1 = #[1]
-- #guard of_nat_be (p:=prime_babybear) (to_nat_be  (p:=prime_babybear) #[255,1]) 2 = #[255,1]

end ByteArray

namespace Bignum

def addCarry (a b : FU8 p) (c : FB p := 0) : FU8 p × FB p :=
  -- behaves well only if p>2^(8+1+1)
  Spec.div_rem (a + b + c) |>.swap

section
attribute [instance high] FU8.instCoeOutValid
lemma addCarry_spec (h : 256 + 256 + 2 < p) (a b : @FU8.Valid p) (c : @FB.Valid p := FB.false) :
  letI o : FU8 p × FB p := addCarry a b c
  (a : ℕ) + (b : ℕ) + (c : ℕ) = (o.2 : ℕ) * 2^8 + (o.1 : ℕ) :=
by
  have hab: ZMod.val a.val + ZMod.val b.val < 256 + 256 := by
    apply Nat.add_lt_add
    · apply a.prop
    · apply b.prop
  let drs := div_rem_spec ((a : FU8 p) + (b : FU8 p) + (c : FU8 p))
  simp at *; simp at drs; simp [addCarry]
  rw [<-drs, ZMod_add_no_overflow, ZMod_add_no_overflow]
  · apply lt_trans
    apply hab
    omega
  · have hc: ZMod.val (a.val + b.val) + ZMod.val c.val < (256 + 256 + 2) := by
      apply Nat.add_lt_add
      · rw [ZMod_add_no_overflow]; try assumption
        apply lt_trans hab; omega
      · exact c.prop
    apply lt_trans hc
    assumption
end

lemma Nat.add_lt_add3 (a b c ta tb tc : ℕ) (ha: a<ta) (hb:b<tb) (hc:c<tc) : a + b + c < ta + tb + tc := by
  apply Nat.add_lt_add
  apply Nat.add_lt_add
  repeat assumption

lemma add_carry_spec_valid (a b :@FU8.Valid p) (c:@FB.Valid p := FB.false)
  (hp: 256+256+2<p) :
  letI o : FU8 p × FB p := add_carry (a:FU8 p) (b:FU8 p) (c:FB p)
  FU8.isValid o.1 ∧ FB.isValid o.2
  := by
  simp [add_carry]
  let drv := div_rem_spec_valid ((a:FU8 p)+(b:FU8 p)+(c:FU8 p))
  simp at drv
  constructor
  apply drv
  simp [FB.isValid, Spec.div_rem]
  rw [Nat.div_mod_eq_div]
  apply Nat.div_lt_of_lt_mul
  -- apply Nat.add_lt_add (b:=256)
  -- let drs := div_rem_spec ((a:FU8 p)+(b:FU8 p)+(c:FU8 p))
  -- simp at drs
  -- simp [drs]
  -- simp
  sorry
  apply lt_trans (b:=256+256+2)
  rw [ZMod_add_no_overflow]
  rw [ZMod_add_no_overflow]
  apply Nat.add_lt_add3
  apply a.prop
  apply b.prop
  apply c.prop
  apply lt_trans (b:=256+256)
  apply Nat.add_lt_add
  apply a.prop
  apply b.prop
  omega
  rw [ZMod_add_no_overflow]
  apply lt_trans (b:=(256+256)+2)
  apply Nat.add_lt_add3
  apply a.prop
  apply b.prop
  apply c.prop
  omega
  apply lt_trans (b:=256+256)
  apply Nat.add_lt_add
  apply a.prop
  apply b.prop
  omega
  assumption

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

-- def addBignum (a b : Array (FU8 p)) : Array (FU8 p) :=
--   addWithCarry a.toList b.toList 0 |>.toArray
-- where
--   addWithCarry (a b : List (FU8 p)) (c : ℕ) : List (FU8 p) :=
--     match a,b,c with
--     | [], [], 0 => []
--     | [], [], c => [c]
--     | (x :: xs), [], c =>
--       let (x,c) := add_carry x 0 c
--       x :: addWithCarry xs [] c
--     | [], (y :: ys), c =>
--       let (y,c) := add_carry 0 y c
--       y :: addWithCarry [] ys c
--     | (x :: xs), (y :: ys), c =>
--       let (t,c) := add_carry x y c
--       t :: addWithCarry xs ys c

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

def UInt8.mul_carry (a b : FU8 p) (c : ZMod p := 0) : FU8 p × (ZMod p) :=
  -- let a : ZMod p := a.toNat
  -- let b : ZMod p := b.toNat
  let o : ZMod p := a.val * b.val + c.val -- 2*8+1 bits
  let (d,r) := Spec.div_rem o
  (r.val,d)

#guard UInt8.mul_carry (p:=prime_babybear) 2 2 = (4,0)
#guard UInt8.mul_carry (p:=prime_babybear) 128 2 = (0,1)
#guard UInt8.mul_carry (p:=prime_babybear) 128 2 = (0,1)

def mul_one_line (a : Array (FU8 p)) (b : FU8 p) (c : ZMod p := 0) : Array (FU8 p) × ZMod p :=
    let (res,c) := aux a.toList c []
    (res.reverse.toArray, c)
  where
  aux (as : List (FU8 p)) (c : ZMod p) (res : List (FU8 p)) : List (FU8 p) × ZMod p :=
    match as with
    | [] => (res,c)
    | a::as =>
      let (ab,c) := UInt8.mul_carry a b c
      aux as c (ab :: res)

-- #guard mul_one_line (p:=prime_babybear) #[1] 1 = (#[1],0)
-- #guard mul_one_line (p:=prime_babybear) #[0,1] 1 = (#[0,1],0)
-- #guard mul_one_line (p:=prime_babybear) #[0,2] 255 = (#[1,254],0)
-- #guard mul_one_line (p:=prime_babybear) #[1,2] 255 = (#[0,254],1)
-- #eval mul_one_line (p:=prime_babybear) #[10,50] 255

-- A = [  200,  150,  2 ]  represents 200·256^2 + 150·256 + 2
-- B = [  180,   30,  3 ]  represents 180·256^2 +  30·256 + 3
-- #guard mul_one_line (p:=prime_babybear) #[200,150,2] 180 = (#[9, 121, 104], 141)
-- #guard mul_one_line (p:=prime_babybear) #[200,150,2]  30 = (#[129, 148, 60], 23)
-- #guard mul_one_line (p:=prime_babybear) #[200,150,2]   3 = (#[89, 194, 6], 2)

#eval ByteArray.to_nat_be (p:=prime_babybear) #[9, 121, 104]
#eval ByteArray.to_nat_be (p:=prime_babybear) #[129, 148, 60]
#eval ByteArray.to_nat_be (p:=prime_babybear) #[89, 194, 6]
#eval add (p:=prime_babybear) #[9, 121, 104] #[129, 148, 60]

-- Zip two lists with a combining function and default fillers
-- def zipWithDefault {α : Type} (f : α → α → α) (dx dy : α) (xs ys : List α) : List α :=
--   aux xs ys
-- where
--   aux (xs ys : List α) : List α :=
--   match xs, ys with
--   | [], [] => []
--   | (x :: xs), [] => f x dy :: aux xs []
--   | [], (y :: ys) => f dx y :: aux [] ys
--   | (x :: xs), (y :: ys) => f x y :: aux xs ys

-- -- Add two bignums aligned least-significant first
-- -- This simply interleaves without final normalization
-- def addAligned : List (FU8 p) → List (FU8 p) → List (FU8 p) :=
--   zipWithDefault (· + ·) 0 0

-- -- Normalize limbs with full carry propagation
-- def normalize (l : Array (FU8 p)) : Array (FU8 p) :=
--   normalizeWithCarry 0 l.toList |>.toArray
-- where
--   normalizeWithCarry (carry : FU8 p) (l : List (FU8 p)) : List (FU8 p) :=
--   match l with
--   | [] => if carry = 0 then [] else [carry % 256, carry / 256]
--   | (x :: xs) =>
--     let (xc, c) := add_carry x carry
--     xc :: normalizeWithCarry c xs

-- -- Shift a partial line by j limbs and append carry at the end
-- def shiftAndCarry (j : ℕ) (part : Array (FU8 p)) (carry : FU8 p) : Array (FU8 p) :=
--     Array.replicate j 0 ++ part ++ [carry]

-- def addShifted (a : Array (FU8 p)) (acc : Array (FU8 p)) (jbj : (FU8 p × ℕ)) : Array (FU8 p) :=
--     let (part, carry) := mul_one_line a jbj.1
--     dbg_trace s!"mul_one_line: ({part}, {carry})"
--     let shifted := shiftAndCarry jbj.2 part carry
--     dbg_trace s!"shifted: {shifted}"
--     dbg_trace s!"addBignum: {addBignum acc shifted}"
--     addAligned acc.toList shifted.toList |>.toArray

-- Assume little-endian
def shiftLeft (n : ℕ) (num : Array (FU8 p)) : Array (FU8 p) :=
  Array.replicate n 0 ++ num

def addBignum (a b : Array (FU8 p)) : Array (FU8 p) :=
  addWithCarry 0 a.toList b.toList |>.toArray
where
  addWithCarry (c : FU8 p) (as bs : List (FU8 p)) :=
    match as,bs with
    | [], [] => if c.val > 0 then [c] else []
    | (a :: as), [] => let (c, l) := Spec.div_rem (a + c); l :: addWithCarry c as []
    | [], (b :: bs) => let (c, l) := Spec.div_rem (b + c); l :: addWithCarry c [] bs
    | (a :: as), (b :: bs) => let (c, l) := Spec.div_rem (a + b + c); l :: addWithCarry c as bs

def mulOneLine (a : Array (FU8 p)) (b : FU8 p) : Array (FU8 p) :=
  go 0 a.toList |>.toArray
where
  go (c : FU8 p) (l : List (FU8 p)) : List (FU8 p) :=
    match l with
    | [] => if c.val > 0 then [c] else []
    | (d :: ds) =>
      letI total := d * b + c
      let (newCarry,newLimb) := Spec.div_rem total
      newLimb :: go newCarry ds

-- #eval mulOneLine (p:=prime_babybear) 256 #[10, 20, 1] 3

def mul (a b : Array (FU8 p)) : Array (FU8 p) :=
  sumPartialProducts 0 b.toList |>.toArray
where
  sumPartialProducts shift (l : List (FU8 p)) :=
    match l with
    | [] => []
    | (limb :: rest) =>
      let partialProduct := mulOneLine a limb
      let shiftedProduct := shiftLeft shift partialProduct
      let remainingSum   := sumPartialProducts (shift + 1) rest
      addBignum shiftedProduct remainingSum.toArray |>.toList

-- TODO need to implement schoolbook multiplication
-- def mul (a b : Array (FU8 p)) : Array (FU8 p) :=
--   let a := b.zipIdx.foldl (addShifted a) (Array.replicate (a.size) 0)
--   dbg_trace s!"before norm: {a}"
--   normalize a

-- #eval mul (p:=prime_babybear) #[0,1] #[0,1]

-- #guard mul (p:=prime_babybear) #[1] #[1] = #[1]
-- #guard mul (p:=prime_babybear) #[0,1] #[0,1] = #[0,1]
-- #guard mul (p:=prime_babybear) #[1,1] #[1,1] = ByteArray.of_nat_be ((256+1) * (256+1)) 2

#eval UInt8.mul_carry (p:=prime_babybear) 200 20  0 -- 160, 15
#eval UInt8.mul_carry (p:=prime_babybear) 150 20 15 -- 199, 11
#eval UInt8.mul_carry (p:=prime_babybear)  10 20 11 -- 211, 0

-- little endian
#guard ByteArray.to_nat_be (p:=prime_babybear) #[10, 20, 1].reverse = 70666
#guard ByteArray.to_nat_be (p:=prime_babybear) #[3, 2, 1].reverse = 66051
#guard 70666 * 66051 = 4667559966
#guard (ByteArray.to_nat_be (p:=prime_babybear) $ mul #[10, 20, 1] #[3, 2, 1] |>.reverse) = 4667559966

#guard ByteArray.to_nat_be (p:=prime_babybear) #[10, 150, 200].reverse = 13145610
#guard ByteArray.to_nat_be (p:=prime_babybear) #[5, 30, 20].reverse = 1318405
#guard 13145610 * 1318405 = 17331237952050
#guard (ByteArray.to_nat_be (p:=prime_babybear) $ mul #[10, 150, 200] #[5, 30, 20] |>.reverse) = 13145610 * 1318405

end Bignum
