import Clap.Spec

namespace Clap

section Wheels

def minBits (x : ℕ) : ℕ :=
  let nb := Nat.log2 x
  if 2^nb < x then nb + 1 else nb

#eval minBits 0
#eval minBits 1
#eval minBits 2

theorem Nat.log2_one : Nat.log2 1 = 0 := by
  simp [Nat.log2_def]

lemma minBits_eq_zero x : minBits x = 0 ↔ x = 0 ∨ x = 1 := by
  apply Iff.intro <;> intro h
  · rcases x with _ | x; simp
    dsimp [minBits] at h; split_ifs at h
    rcases x with _ | x
    · simp
    · grind
  · rcases h with h' | h' <;>
      rw [h']; simp [minBits]; try apply Nat.log2_one

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

lemma minBytes_eq_zero x : minBytes x = 0 ↔ x = 0 ∨ x = 1 := by
  apply Iff.intro <;> intro h
  · rcases x with _ | x; simp
    dsimp [minBytes] at h
    by_cases h' : minBits (x + 1) % 8 = 0
    · rw [if_pos h'] at h
      rcases (Nat.dvd_of_mod_eq_zero h') with w
      have : minBits (x + 1) = 0 := by apply Nat.eq_zero_of_dvd_of_div_eq_zero <;> assumption
      apply minBits_eq_zero (x + 1) |>.mp at this
      assumption
    · rw [if_neg h'] at h
      have := (@Nat.div_eq_zero_iff_lt 8 (minBits (x + 1)) (by simp))
      sorry
  · rcases h with h' | h' <;> rw [h'] <;> simp [minBytes, minBits]
    split_ifs <;> rw [Nat.log2_one] at *; grind

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

variable {p : ℕ} [Fact (Nat.Prime p)]

abbrev FB p := ZMod p

namespace FB

def isValid (x : FB p) : Prop := x.val < 2

def Valid : Type := {x : FB p // isValid x } -- TODO only for specs

instance : CoeOut (FB p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

-- instance : CoeOut (@Valid p) (FB p) where
--   coe x := x.val

def true (h : p ≠ 1): @Valid p :=
  ⟨1, by rw [isValid, ZMod.val_one'']; simp; assumption⟩

def false : @Valid p :=
  ⟨0, by simp [isValid]⟩

end FB

abbrev FU8 p := ZMod p

instance : ToString (FU8 p) where
  toString a := a.val

namespace FU8

def isValid (x : FU8 p) : Prop := x.val < 2^8

def Valid : Type := {x : FU8 p // isValid x } -- TODO only for specs

instance : CoeOut (FU8 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) ℕ where
  coe x := x.val

def mk (x : FU8 p) : Option Unit := Spec.assert_range 8 x

omit [Fact (Nat.Prime p)] in
lemma mk_some (x : FU8 p) (h : x.val < 2^8) : x.mk = some () := by
  simp [mk, Spec.assert_range]; assumption

end FU8

#guard Spec.div_rem (p := prime_babybear) 200 = (0, 200)
#guard Spec.div_rem (p := prime_babybear) (2 * 256) = (2, 0)
#guard Spec.div_rem (p := prime_babybear) 512 = (2, 0)

-- lemma div_rem_spec (a d r : ZMod p) :
--   Spec.div_rem a = some (d, r) → a = d * 2^8 + r :=
-- by simp [Spec.div_rem]; grind

lemma div_rem_spec (a : ZMod p) :
  letI o := Spec.div_rem a; a.val = o.1 * 256 + o.2 := by
  simp [Spec.div_rem]
  rw [Nat.mod_mod_eq_mod_of_lt_right, Nat.div_mod_eq_div]
  omega
  repeat apply ZMod.val_lt

lemma stupid (hh : 256 < p) : (256 : ZMod p) ≠ (0 : ZMod p) := by
  rw [ne_eq, ←ZMod.val_eq_zero]
  change ¬ ((Nat.cast 256 : ZMod _)).val = 0
  rw [ZMod.val_cast_of_lt hh]
  omega

lemma lol (hh : 256 < p) (a : ZMod p) : a * (2^8 : ZMod p) / (2^8 : ZMod p) = a := by
  ring_nf
  have : a * 256⁻¹ * 256 = a * (256 * 256⁻¹) := by grind
  rw [this, Field.mul_inv_cancel] <;> simp
  rw [←ZMod.val_eq_zero]
  change ¬ ((Nat.cast 256 : ZMod _)).val = 0
  rw [ZMod.val_cast_of_lt hh]
  omega

-- lemma div_rem_spec_valid (a d r : ZMod p)
--   (hp : 256 < p)
--   (ha : FU8.isValid a)
--   (hs : Spec.div_rem a = some (d, r)):
--   FU8.isValid r ∧ FB.isValid d :=
-- by
--   split_ands <;> simp [Spec.div_rem, FU8.isValid, FB.isValid] at * <;> rcases hs with ⟨hl, hr⟩
--   · rw [lol hp] at hr; simp at *; rw [←hr]
--     rw [ZMod.val_zero]; omega
--   · have hh : a * (2^8 : ZMod p)⁻¹ = 1 ∨ a * (2^8 : ZMod p)⁻¹ = 0 := by

lemma div_rem_spec_valid (a : ZMod p) :
  letI o := Spec.div_rem a; FU8.isValid o.2 := by
  simp [Spec.div_rem, FU8.isValid]
  rw [Nat.mod_mod_eq_mod_of_lt_right]
  omega; apply ZMod.val_lt

lemma div_rem_valid_spec_valid (a : ZMod p) (h₁ : FU8.isValid a) (h₂ : 256 < p) :
  letI o := Spec.div_rem a; FU8.isValid o.2 ∧ FB.isValid o.1 :=
by
  split_ands
  · apply div_rem_spec_valid
  · simp [Spec.div_rem, FB.isValid]
    rw [Nat.div_mod_eq_div] <;> simp [FU8.isValid] at h₁
    · apply Nat.div_lt_of_lt_mul; omega
    · omega

namespace ByteArray

-- This works if 2^8 < p ?
def ofNat (x len : ℕ) : Array (FU8 p) := aux x len
where
  aux (x len : ℕ) : Array (FU8 p) :=
    let d : ℕ := x / 2^8
    let r : ℕ := x % 2^8
    if len = 0 then #[] else ⟨r :: (aux d (len - 1)).toList⟩

#guard (ofNat (p := prime_babybear) (255 + 1)  2) = #[0,1]
#guard (ofNat (p := prime_babybear) (2^16 + 2) 3) = #[2,0,1]
#guard (ofNat (p := prime_babybear) (2^16 + 2) 4) = #[2,0,1,0]

def toNat (bs : Array (FU8 p)) : ℕ :=
  bs.foldr (fun (b : FU8 p) acc => acc * 2^8 + b) 0

#guard toNat (p := prime_babybear) #[1] = 1
#guard toNat (p := prime_babybear) #[1,255] = 255*256+1
#guard toNat (p := prime_babybear) #[1,2,3] = 3*256*256 + 2*256 + 1
#guard toNat (p := prime_babybear) #[2,0,1,0] = 65536 + 2

lemma eq_ofNat_toNat (x len : ℕ) (h : minBytes x ≤ len) :
  toNat (ofNat (p := p) x len) = x :=
by
  induction len
  · simp [toNat, ofNat, ofNat.aux]; simp at h; rw [minBytes_eq_zero] at h
    sorry
  · sorry

#guard let n : ℕ := 255  + 1; toNat (ofNat (p := prime_babybear) n 2) = n
#guard let n : ℕ := 2^16 + 2; toNat (ofNat (p := prime_babybear) n 3) = n
#guard let n : ℕ := 2^16 + 2; toNat (ofNat (p := prime_babybear) n 4) = n

#guard ofNat (p := prime_babybear) (toNat (p := prime_babybear) #[1]) 1 = #[1]
#guard ofNat (p := prime_babybear) (toNat (p := prime_babybear) #[1,255]) 2 = #[1,255]

end ByteArray

namespace Bignum

def addCarry (a b : FU8 p) (c : FB p := 0) : FU8 p × FB p :=
  -- behaves well only if p>2^(8+1+1)
  Spec.div_rem (a + b + c) |>.swap

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

private
lemma Nat.add_lt_add3 (a b c ta tb tc : ℕ) (ha: a < ta) (hb : b < tb) (hc : c < tc) :
  a + b + c < ta + tb + tc := by
  apply Nat.add_lt_add
  apply Nat.add_lt_add
  repeat assumption

lemma addCarry_spec_valid (a b : @FU8.Valid p) (c : @FB.Valid p := FB.false) (h : 256 + 256 + 2 < p) :
  letI o : FU8 p × FB p := addCarry a b c; FU8.isValid o.1 ∧ FB.isValid o.2 :=
by
  simp [addCarry]
  let drv := div_rem_spec_valid ((a : FU8 p) + (b : FU8 p) + (c : FB p))
  simp at drv; split_ands; apply drv
  sorry
  -- simp [FB.isValid, Spec.div_rem]
  -- rw [Nat.div_mod_eq_div]
  -- · simp [FU8.isValid, Spec.div_rem] at drv
  --   rw [Nat.mod_mod_eq_mod_of_lt_right] at drv
  --   rw [Nat.div_lt_iff_lt_mul]

    --sorry
    -- rw [Nat.mod_mod_eq_mod_of_lt_right] at drv
  -- . apply Nat.div_lt_of_lt_mul
  --   rw [ZMod_add_no_overflow, ZMod_add_no_overflow]
  --   · apply lt_trans (b := 256 + 256 + 2)
  --   · apply Nat.add_lt_add
  -- apply Nat.add_lt_add (b:=256)
  -- let drs := div_rem_spec ((a:FU8 p)+(b:FU8 p)+(c:FU8 p))
  -- simp at drs
  -- simp [drs]
  -- simp
  -- · apply lt_trans (b := 256 + 256 + 2)
  --   · rw [ZMod_add_no_overflow, ZMod_add_no_overflow]
  --     · apply Nat.add_lt_add3; apply a.prop; apply b.prop; apply c.prop
  --     · apply (lt_trans (b := 256 + 256))
  --       apply Nat.add_lt_add; apply a.prop; apply b.prop; omega
  --     · rw [ZMod_add_no_overflow]
  --       · apply lt_trans (b := (256 + 256) + 2); apply Nat.add_lt_add3
  --         apply a.prop; apply b.prop; apply c.prop; omega
  --       · apply lt_trans (b := 256 + 256); apply Nat.add_lt_add
  --         apply a.prop; apply b.prop; omega
  --   · assumption

#guard addCarry (p := prime_babybear) 1 1 = (2,0)
#guard addCarry (p := prime_babybear) 255 2 = (1,1)
#guard addCarry (p := prime_babybear) 255 3 = (2,1)
#guard addCarry (p := prime_babybear) 255 255 1 = (255,1)
#guard addCarry (p := prime_babybear) 300 300 5 = (93,2) -- nonsense

open Spec in
def ex (a b : FU8 p) : Option Unit := do
  FU8.mk a
  FU8.mk b
  let (_o,c') := addCarry a b
  eq0 c'
  accept ()

-- Assume little-endian
def shiftLeft (n : ℕ) (num : Array (FU8 p)) : Array (FU8 p) :=
  Array.replicate n 0 ++ num

def addBignum (a b : Array (FU8 p)) : Array (FU8 p) :=
  addWithCarry 0 a.toList b.toList |>.toArray
where
  addWithCarry (c : FU8 p) (as bs : List (FU8 p)) : List (FU8 p) :=
    match as,bs with
    | [], [] => if c.val > 0 then [c] else []
    | (a :: as), [] => let (c, l) := Spec.div_rem (a + c); l :: addWithCarry c as []
    | [], (b :: bs) => let (c, l) := Spec.div_rem (b + c); l :: addWithCarry c [] bs
    | (a :: as), (b :: bs) => let (c, l) := Spec.div_rem (a + b + c); l :: addWithCarry c as bs

section ex
open ByteArray

def ofNat' x := ofNat (p:=prime_babybear) x (minBytes x)
def toNat' x := toNat (p:=prime_babybear) x

#guard ofNat' 1234 = #[210, 4]
#guard ofNat' 4321 = #[225, 16]
#guard 1234 + 4321 = 5555
#guard ofNat' 5555 = #[179, 21]

#eval addBignum (ofNat' 45536) (ofNat' 19999)

#guard addBignum (ofNat' 1234) (ofNat' 4321) = ofNat' 5555
#guard toNat' (addBignum (ofNat' 1234) (ofNat' 4321)) = 5555

#guard addBignum (ofNat' 0) (ofNat' 0) = ofNat' 0
#guard addBignum (ofNat' 189274) (ofNat' 893475) = ofNat' (189274 + 893475)
#guard addBignum (ofNat' 987654321) (ofNat' 123456789) = ofNat' (987654321 + 123456789)
end ex

def mulCarry (a b : FU8 p) (c : ZMod p := 0) : FU8 p × (ZMod p) :=
  --let o : ZMod p :=  -- 2*8+1 bits
  Spec.div_rem (a * b + c) --|>.swap

def mulOneLine (a : Array (FU8 p)) (b : FU8 p) : Array (FU8 p) :=
  aux 0 a.toList |>.toArray
where
  aux (c : FU8 p) (l : List (FU8 p)) : List (FU8 p) :=
    match l with
    | [] =>
      if c.val > 0 then
        -- We need better way to model FU8, here c.val can be 256. Check why addBignum deals
        -- correctly with this
        if c.val > 2^8 - 1 then
          let (cr, lm) := Spec.div_rem c; [lm, cr]
        else [c]
      else []
    | (d :: ds) =>
      let (cr, lm) := mulCarry d b c
      lm :: aux cr ds

section ex
open ByteArray

#guard 15 * 2^27 + 1 = 2013265921
#guard 12345 * 54321 =  670592745
#guard 12345*1359 = 16776855
#guard (ofNat' $ 12345*1359) = #[151, 254, 255]
#guard 12345*1360 = 16789200
#guard (ofNat' $ 12345*1360) = #[208, 46, 0, 1]
#guard (ofNat' 12345) = #[57, 48]
#guard mulOneLine (ofNat' 12345) 1359 = #[151, 254, 255]
#guard mulOneLine (ofNat' 12345) 1360 = (ofNat' $ 12345*1360)
--#guard mulOneLine (ofNat' 12345) 1360 = #[208, 46, 256] -- wrong
#guard mulOneLine (p := prime_babybear) #[10, 20, 1] 3 = #[30, 60, 3]
#guard mulOneLine (ofNat' 12345) 5 = (ofNat' $ 12345*5)
#guard mulOneLine (ofNat' 12345) 1359 = (ofNat' $ 12345*1359)
#guard mulOneLine (ofNat' $ 2^16 + 1) 128 = (ofNat' $ (2^16 + 1) * 128)
end ex

def mulBignum (a b : Array (FU8 p)) : Array (FU8 p) :=
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

section ex
open ByteArray

#guard mulBignum (ofNat' 70666) (ofNat' 66051) = ofNat' (70666 * 66051)
#guard mulBignum (ofNat' 13145610) (ofNat' 1318405) = ofNat' (13145610 * 1318405)
end ex

end Bignum

end Clap
