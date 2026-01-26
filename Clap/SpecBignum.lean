import Clap.Spec
import Mathlib.Data.List.DropRight

namespace Clap

section Wheels

def minBits (x : ℕ) : ℕ :=
  if x = 0 then 1 else
  let nb := Nat.log2 x
  if 2^nb ≤ x then nb + 1 else nb

-- theorem Nat.log2_one : Nat.log2 1 = 0 := by
--   simp [Nat.log2_def]

-- lemma minBits_eq_zero x : minBits x = 0 ↔ x = 0 ∨ x = 1 := by
--   apply Iff.intro <;> intro h
--   · rcases x with _ | x; simp
--     dsimp [minBits] at h; split_ifs at h
--     rcases x with _ | x
--     · simp
--     · grind
--   · rcases h with h' | h' <;>
--       rw [h']; simp [minBits]; try apply Nat.log2_one

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

#eval minBytes 0           -- 1
#eval minBytes (256^1 - 1) -- 1

#eval minBytes (256^1)     -- 2
#eval minBytes (256^2 - 1) -- 2

#eval minBytes (256^2)     -- 3
#eval minBytes (256^3 - 1) -- 3

#eval minBytes (256^3)     -- 4
#eval minBytes (256^4 - 1) -- 4

#eval minBytes (256^4)     -- 5
#eval minBytes (256^5 - 1) -- 5

-- lemma minBytes_eq_zero x : minBytes x = 0 ↔ x = 0 ∨ x = 1 := by
--   apply Iff.intro <;> intro h
--   · rcases x with _ | x; simp
--     dsimp [minBytes] at h
--     by_cases h' : minBits (x + 1) % 8 = 0
--     · rw [if_pos h'] at h
--       rcases (Nat.dvd_of_mod_eq_zero h') with w
--       have : minBits (x + 1) = 0 := by apply Nat.eq_zero_of_dvd_of_div_eq_zero <;> assumption
--       apply minBits_eq_zero (x + 1) |>.mp at this
--       assumption
--     · rw [if_neg h'] at h
--       have := (@Nat.div_eq_zero_iff_lt 8 (minBits (x + 1)) (by simp))
--       sorry
--   · rcases h with h' | h' <;> rw [h'] <;> simp [minBytes, minBits]
--     split_ifs <;> rw [Nat.log2_one] at *; grind

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

-- lemma eq_ofNat_toNat (x len : ℕ) (h : minBytes x ≤ len) :
--   toNat (ofNat (p := p) x len) = x :=
-- by
--   induction len
--   · simp [toNat, ofNat, ofNat.aux]; simp at h; rw [minBytes_eq_zero] at h
--     sorry
--   · sorry

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

-- ugly. If we try to remove trailling zeros from this zero number [0,0,0] it returns []
-- which is wrong.
def removeTraillingZeros (a : List (FU8 p)) : List (FU8 p) :=
  let l := List.rdropWhile (· = 0) a
  if l.isEmpty then [0] else l

-- Correct way?
instance : Ord (ZMod p) where
  compare x y := compare x.val y.val

-- Compare two BigNums (Little-Endian). We reverse them to compare MSB first.
def compareBignum (a b : Array (FU8 p)) : Ordering :=
  let a' := removeTraillingZeros a.toList
  let b' := removeTraillingZeros b.toList
  List.compareLex compare a' b'

section ex
open ByteArray Ordering

#guard compareBignum (ofNat' 70666) (ofNat' 66051) = gt
#guard compareBignum (ofNat' 1318405) (ofNat' 13145610) = lt
#guard compareBignum (p := prime_babybear) #[0] #[0] = eq
#guard compareBignum (p := prime_babybear) #[1, 0, 0] #[1, 0, 0] = eq
end ex

-- Subtracts ys from xs (xs - ys). Assumes xs >= ys
def sub' (a b : Array (FU8 p)) : Array (FU8 p) :=
  let rec loop (xs ys : List (FU8 p)) (borrow : FU8 p) : List (FU8 p) :=
    match xs, ys with
    | [], [] => []
    | x :: xt, [] =>
      if borrow == 0 then x :: xt
      else if x.val >= borrow then (x - borrow) :: xt
      else (2^8 - borrow + x) :: loop xt [] 1
    | x :: xt, y :: yt =>
      let y_adj := y + borrow
      if x.val >= y_adj then
        (x - y_adj) :: loop xt yt 0
      else
        (2^8 + x - y_adj) :: loop xt yt 1
    | [], _ => []
  ⟨removeTraillingZeros (loop a.toList b.toList 0)⟩

def subBignum (xs ys : Array (FU8 p)) : Option (Array (FU8 p)) :=
  (List.toArray <$> removeTraillingZeros <$> subWithBorrow 0 xs.toList ys.toList)
where
  subWithBorrow b xs ys := do
    match b, xs, ys with
    -- Case 1: Both lists empty. If borrow > 0, we had an underflow, precondition violated
    | 0, [], [] => .some []
    | _, [], [] => .none

    -- Case 2: ys runs out. We still might have a borrow to subtract from xs.
    | b, (x :: xs), [] =>
      if x.val ≥ b then .some ((x - b) :: xs) -- No new borrow needed, rest of xs remains as is.
      else (x + 2^8 - b) :: (← subWithBorrow 1 xs [])

    -- Case 3: xs runs out but ys remains. Impossible if xs >= ys.
    | _, [], (_ :: _) => .none

    -- Case 4: Both lists have limbs.
    | b, (x :: xs), (y :: ys) =>
      let s := y + b
      -- No borrow needed for next step
      if x.val ≥ s then (x - s) :: (← subWithBorrow 0 xs ys)
      -- Borrow needed: "Add" base to current digit, "borrow" 1 from next
      else ((x + 2^8) - s) :: (← subWithBorrow 1 xs ys)


section ex
open ByteArray Ordering

#guard subBignum (ofNat' 4321) (ofNat' 1234) = .some (ofNat' (4321 - 1234))
#guard subBignum (ofNat' 4321) (ofNat' 1234) = ofNat' (4321 - 1234)
#guard subBignum (ofNat' 1234) (ofNat' 4321) = .none
#guard subBignum (ofNat' 1) (ofNat' 2) = .none
#guard subBignum (ofNat' 1234) (ofNat' 1234) = ofNat' 0

#guard sub' (ofNat' 4321) (ofNat' 1234) = (ofNat' (4321 - 1234))
#guard sub' (ofNat' 4321) (ofNat' 1234) = ofNat' (4321 - 1234)
#eval sub' (ofNat' 1234) (ofNat' 4321) -- nonsense
#eval sub' (ofNat' 1) (ofNat' 2) -- nonsense
#guard subBignum (ofNat' 1234) (ofNat' 1234) = ofNat' 0

-- identity (subtracting zero)
-- how to correctly deal with #[] and #[0] being equal
#guard subBignum (p := prime_babybear) #[5, 4, 3] #[] = .some #[5, 4, 3]
#guard subBignum (p := prime_babybear) #[5, 4, 3] #[0] = .some #[5, 4, 3]
-- substract self
#guard subBignum (p := prime_babybear) #[2, 1] #[2, 1] = .some #[0]
#guard subBignum (p := prime_babybear) #[2, 1] #[2, 1] ≠ .some #[]
-- "ripple" borrow
#guard subBignum (p := prime_babybear) #[0, 0, 1] #[1] = .some #[255,255]
#guard subBignum (ofNat' (256^2)) (ofNat' 1) = .some (ofNat' (256^2 - 1))
-- Simple No-Borrow
#guard subBignum (p := prime_babybear) #[9, 9, 9] #[1, 2, 3] = .some #[8, 7, 6]
#guard subBignum (ofNat' 592137) (ofNat' 197121) = .some (ofNat' (592137 - 197121))
-- length mismatch (small y)
#guard subBignum (p := prime_babybear) #[57, 48] #[5] = .some #[(57 - 5), 48]
-- length mismatch with borrow
#guard subBignum (p := prime_babybear) #[0, 1] #[1] = .some #[255]
-- alternating borrows
#guard subBignum (ofNat' 84018434) (ofNat' 196611) = .some (ofNat' (84018434 - 196611))
#guard subBignum (p := prime_babybear) #[2, 5, 2, 5] #[3, 0, 3, 0] = .some #[255, 4, 255, 4]
-- multi-limb borrow (recursive)
#guard subBignum (ofNat' 196613) (ofNat' 6) = .some (ofNat' (196613 - 6))
#guard subBignum (p := prime_babybear) #[5, 0, 3] #[6] = .some #[255, 255, 2]
end ex

def doubleAndAdd (n : Array (FU8 p)) (bit : FU8 p) : Array (FU8 p) :=
  let rec loop (xs : List (FU8 p)) (carry : FU8 p) : List (FU8 p) :=
    match xs with
    | [] => if carry.val > 0 then [carry] else []
    | x :: xt =>
      let val := (x * 2) + carry
      let (newCarry, newLimb) := Spec.div_rem val
      newLimb :: loop xt newCarry
  ⟨loop n.toList bit⟩

-- /--
--   Computes (x % m) using Schoolbook Long Division.
--   Structure:
--   1. Process `x` limb-by-limb from MSB (Head of reversed list) to LSB.
--   2. Inside each limb, process bits from 7 down to 0.
--   3. Perform "Shift, Add, Check-Subtract" at every bit.
-- -/
-- def modBignum (x m : Array (FU8 p)) : Array (FU8 p) :=
--   if removeTraillingZeros m.toList = [0] then #[0] else
--   let lala := Array.foldl (fun rem limb ↦ processLimb rem limb 7) (#[0] : Array (FU8 p))
--   lala
-- where
--   step (rem : Array (FU8 p)) (bit : FU8 p) : Array (FU8 p) :=
--     let remShifted := doubleAndAdd rem bit
--     if compareBignum remShifted m = Ordering.gt then sub' remShifted m else remShifted
--   processLimb (rem : Array (FU8 p)) (limb bitIdx : ℕ) : Array (FU8 p) :=
--     let bit := (limb / (2 ^ bitIdx)) % 2
--     let rem' := step rem bit
--     match bitIdx with
--     | 0 => rem'
--     | k + 1 => processLimb rem' limb k



-- section ex
-- open ByteArray

-- #eval 266 % 5
-- #eval modBignum (p := prime_babybear) #[10, 1] #[5]

-- #eval toNat' #[10, 1]
-- #eval toNat' #[0, 5, 1]

-- end ex

end Bignum

-- ==========================================
-- Byte alternative example
-- ==========================================

namespace ByteBit

abbrev Bit := Fin 2
abbrev Byte := Fin 256

-- As long as p > 65536 (256*256) > 65537
-- we have enought space to do every operation we want
#guard minBytes (255 + 255 + 255) ≤ 2 -- add carry
#guard minBytes (255*2 + 255)     ≤ 2 -- double and add
#guard minBytes (255*255 + 255)   ≤ 2 -- mul carry

section exampleField
abbrev Fp := ZMod 65537

-- We can embed Byte and Bit into the field
instance : Coe Byte Fp where
  coe b := b.val

instance : Coe Bit Fp where
  coe b := b.val

theorem byte_embeds_field (b : Byte) : (b : Fp).val = b.val := by
  apply Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by simp))

theorem bit_embeds_field (b : Bit) : (b : Fp).val = b.val := by
  apply Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by simp))

end exampleField

abbrev Bignum := List Byte

-- lemma carryOut_bit {a b c} (ha : a ≤ 255) (hb : b ≤ 255) (hc : c ≤ 1) :
--   (a + b + c) / 256 < 2 :=
-- by
--   have : a + b + c ≤ 511 := by
--     apply Nat.le_trans (Nat.add_le_add (Nat.add_le_add ha hb) hc)
--     decide
--   apply Nat.div_lt_of_lt_mul
--   omega

def fullAdd (a b : Byte) (carryIn : Bit := 0) : Byte × Bit :=
  let rawSum := a.val + b.val + carryIn.val
  let sumVal := rawSum % 256 -- We can use Spec.div_rem here
  let carryOut := rawSum / 256
  have h_carry : carryOut < 2 := by
    have ha : a.val ≤ 255     := Nat.le_of_lt_succ a.isLt
    have hb : b.val ≤ 255     := Nat.le_of_lt_succ b.isLt
    have hc : carryIn.val ≤ 1 := Nat.le_of_lt_succ carryIn.isLt
    have h_sum : rawSum ≤ 511 := by
      apply Nat.le_trans (Nat.add_le_add (Nat.add_le_add ha hb) hc); decide
    simp [carryOut]; apply Nat.div_lt_of_lt_mul; omega
  (⟨sumVal, Nat.mod_lt _ (by decide)⟩, ⟨carryOut, h_carry⟩)

#guard fullAdd 1 1 = (2,0)
#guard fullAdd 255 2 = (1,1)
#guard fullAdd 255 3 = (2,1)
#guard fullAdd 255 255 1 = (255,1)
-- #guard fullAdd 0 0 1 = fullAdd 256 256 5

def ofNat' (x len : ℕ) : Bignum :=
  let d := x / 256
  let r := x % 256
  if len = 0 then [] else ⟨r, Nat.mod_lt _ (by decide)⟩ :: (ofNat' d (len - 1))

def ofNat (n : ℕ) : Bignum :=
  if n == 0 then []
  else
    let digit := n % 256
    let rest := n / 256
    ⟨digit, Nat.mod_lt _ (by decide)⟩ :: ofNat rest
decreasing_by
  apply Nat.div_lt_self <;> grind

#guard ofNat (255 + 1)  = [0,1]
#guard ofNat (2^16 + 2) = [2,0,1]

def toNat : Bignum → ℕ :=
  List.foldr (fun b acc => acc * 256 + b) 0

#guard toNat [0,1]     = (255 + 1)
#guard toNat [2,0,1]   = (2^16 + 2)
#guard toNat [2,0,1,0] = (2^16 + 2)

instance (n : ℕ) : OfNat Bignum n where
  ofNat := ofNat n

def Bignum.add (a b : Bignum) : Bignum :=
  loop a b 0
where
  loop (xs ys : List Byte) (c : Bit) : Bignum :=
    match xs, ys with
    -- Case 1: Both lists finished.
    -- If there is a remaining carry, append a new limb [1].
    | [], [] => if c.val == 1 then [⟨1, by decide⟩] else []

    -- Case 2: 'a' is longer than 'b'.
    -- Continue adding carry to 'a' (effectively adding 0 from b).
    -- | x :: xs, [] => let (sum, newC) := fullAdd x 0 c; sum :: loop xs [] newC
    | x :: xs, [] =>
      if c.val == 0 then x :: xs -- stop recursion if no carry
      else let (sum, newC) := fullAdd x 0 c; sum :: loop xs [] newC

    -- Case 3: 'b' is longer than 'a'.
    | [], y :: ys => let (sum, newC) := fullAdd 0 y c; sum :: loop [] ys newC

    -- Case 4: Standard addition of two limbs.
    | x :: xs, y :: ys => let (sum, newC) := fullAdd x y c; sum :: loop xs ys newC

#guard (40 : Bignum).add 2 = 42

-- identity
#guard Bignum.add 0 0 = 0
#guard Bignum.add 12345 0 = 12345
#guard Bignum.add 0 67890 = 67890
-- single limb no carry
#guard Bignum.add 10 20 = 30
-- single limb overflow
#guard Bignum.add  250   10  =  260
#guard Bignum.add [250] [10] = [4,1]
-- multi-limb propagation
#guard Bignum.add  255   1  =  256
#guard Bignum.add [255] [1] = [0,1]
-- long ripple
#guard Bignum.add   65535     1  =   65536
#guard Bignum.add [255, 255] [1] = [0, 0, 1]
-- left larger
-- #eval ofNat 100000 -- [160, 134, 1]
-- #eval ofNat 5 -- [5]
#guard Bignum.add 100000 5 = 100005 -- [165, 134, 1]
-- right larger
-- #eval ofNat 200000 -- [64, 13, 3]
-- #eval ofNat 10 -- [10]
#guard Bignum.add 200000 10 = 200010 -- [74, 13, 3]
-- boundary carry at the end
#guard Bignum.add  255   255  =    510
#guard Bignum.add [255] [255] = [254, 1]
-- alternating bit
#guard Bignum.add 43690 21845 = 65535

-- def mulCarry (a b : FU8 p) (c : ZMod p := 0) : FU8 p × (ZMod p) :=
--   --let o : ZMod p :=  -- 2*8+1 bits
--   Spec.div_rem (a * b + c) --|>.swap

/--
  Multiply (a * b + (carry = 0)).
  Returns (low (res), high (carry)) such that val = low + high * 256.
-/
def mulCarry (a b : Byte) (c : Byte := 0) : Byte × Byte :=
  let rawMul := a.val * b.val + c.val
  let loVal := rawMul % 256
  let hiVal := rawMul / 256
  have h_hi : hiVal < 256 := by
    have ha : a.val ≤ 255 := Nat.le_of_lt_succ a.isLt
    have hb : b.val ≤ 255 := Nat.le_of_lt_succ b.isLt
    have hc : c.val ≤ 255 := Nat.le_of_lt_succ c.isLt
    have h_mul : a.val * b.val ≤ 65025 := Nat.mul_le_mul ha hb
    have h_total : rawMul ≤ 65280 := by
      apply Nat.le_trans (Nat.add_le_add h_mul hc)
      decide
    simp [hiVal]; apply Nat.div_lt_of_lt_mul; omega
  (⟨loVal, Nat.mod_lt _ (by decide)⟩, ⟨hiVal, h_hi⟩)

def mulOneLine (xs : Bignum) (s : Byte) : Bignum :=
  loop xs 0
where
  loop i carry :=
    match i with
    | [] => if carry > 0 then [carry] else []
    | x :: xs =>
      let (newLimb, newCarry) := mulCarry x s carry
      newLimb :: loop xs newCarry

-- TODO: how to deal with multiple zero representation
#guard mulOneLine 0 0 = 0
#guard mulOneLine 65535 0 = [0, 0]
#guard mulOneLine 0 255 = []
#guard mulOneLine 65535 1 = 65535
#guard mulOneLine 1 253 = 253
#guard mulOneLine 65535 2 = ofNat (65535 * 2)
#guard mulOneLine 1000 250 = ofNat (1000 * 250)
#guard mulOneLine 65535 255 = ofNat (65535 * 255)
#guard mulOneLine 10 10 = 100
#guard mulOneLine 222 2 = 444
#guard mulOneLine 255 255 = 65025
#guard mulOneLine 65537 3 = 196611

def Bignum.mul (xs ys : Bignum) : Bignum :=
  match ys with
  | [] => [] -- x * 0
  | y :: ys =>
    let term := mulOneLine xs y
    let rest := mul xs ys
    let shifted := if rest.isEmpty then [] else zeroByte :: rest
    term.add shifted
where
  zeroByte : Byte := ⟨0, by decide⟩

#guard Bignum.mul 0 65535 = []
#guard Bignum.mul 65535 0 = []
#guard Bignum.mul 1 123456789 = 123456789
#guard Bignum.mul 123456789 1 = 123456789
#guard Bignum.mul 10 10 = 100
#guard Bignum.mul 255 255 = 65025
#guard Bignum.mul 256 256 = 65536
#guard Bignum.mul 2 100000 = 200000
#guard Bignum.mul 100000 2 = 200000
#guard Bignum.mul 65535 65535 = 4294836225
#guard Bignum.mul 12345 67890 = 838102050

end ByteBit

-- exponentiation by 65537 = 2^16 - 1, which means: square the base 16 times plus
-- a final multiplication
-- def fpPow65537Mod

end Clap
