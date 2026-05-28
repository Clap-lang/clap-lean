import Clap.Primes
import Clap.Spec

namespace Clap.Lang

export Clap.Spec.Compiler (
  accept
  eq0
  share
  isZero
  num2bits
  fpMul
  bits2numV)

variable {p : ℕ}

abbrev F p := ZMod p
abbrev FB p := F p

namespace F

instance : Inhabited (F p) where
  default := 42

def assert_range (w : ℕ) (e : F p) : Option Unit := do
  let _ <- num2bits w e ; ()

def assert_eq (a b : F p) : Option Unit := do
  eq0 (a - b)

def eq (a b : F p) : Option (FB p) :=
  isZero (a - b)

def dotProduct {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

/-- Gated assertion: asserts `constraint == 0` only when `guard == 1` -/
def guardedEq0 (guard : FB p) (constraint : F p) : Option Unit :=
  eq0 (guard * constraint)

/-- Gated equality: asserts `a == b` only when `guard == 1` -/
def guardedAssertEq (guard : FB p) (a b : F p) : Option Unit :=
  guardedEq0 guard (a - b)

def conditionalSwap (sel : FB p) (a b : F p) : F p :=
  (a - b) * sel + b

end F

namespace FB

def true : FB p := 1

def false : FB p := 0

def ofBool (b:Bool) : FB p :=
  if b then FB.true else FB.false

instance : Inhabited (FB p) where
  default := false

def eq (a b : FB p) : Option (FB p) :=
  F.eq a b

def assertBool (f: FB p) : Option Unit :=
  eq0 (f * (1 - f))

def and (a b : FB p) : FB p := a * b

instance : HAnd (FB p) (FB p) (FB p) where
  hAnd := and

def or (a b : FB p) : FB p := a + b - a * b

instance : HOr (FB p) (FB p) (FB p) where
  hOr := or

def not (a : FB p) : FB p := 1 - a

def xor (a b : FB p) : FB p := a + b - 2 * a * b

instance : HXor (FB p) (FB p) (FB p) where
  hXor := xor

def assert (a : FB p) : Option Unit := do
  eq0 (not a)

def assert_eq (a b : FB p) : Option Unit := do
  F.assert_eq a b

def conditionallyAssert (antecedent consequent : FB p) : Option Unit :=
    -- a → c ≡ ¬(a ∧ ¬c)
    eq0 (antecedent &&& FB.not consequent)

end FB

namespace Spec.FB

variable [Fact (Nat.Prime p)]

def valid (a: ZMod p) : Prop := a = FB.false ∨ a = FB.true

def toBool (f:ZMod p) : Bool :=
  if f = FB.false then false else true

def valid_ofBool (b:Bool) : valid (FB.ofBool (p:=p) b) := by
  simp [valid,FB.ofBool,FB.false,FB.true]

lemma right_inv (f: ZMod p) (h : valid f) : FB.ofBool (toBool f) = f := by
  aesop (add simp [toBool,FB.ofBool,valid])

lemma left_inv (b: Bool) : toBool (p:=p) (FB.ofBool b) = b := by
  aesop (add simp [toBool,FB.ofBool,FB.true,FB.false])

-- noncomputable def boolEquiv :
--   Equiv Bool (ZMod p)
-- where
--   toFun := ofBool
--   invFun := toBool
--   left_inv := left_inv
--   right_inv := right_inv

lemma eq_equiv (a b : ZMod p) (ha : valid a) (hb : valid b) :
  FB.eq a b = some (FB.ofBool ((toBool a) = (toBool b))) := by
  unfold FB.eq F.eq
  aesop (add simp [left_inv,right_inv,toBool,FB.and,FB.false,FB.true,valid,isZero])

lemma and_equiv (a b : ZMod p) (ha : valid a) (hb : valid b) :
  a &&& b = FB.ofBool (toBool a && toBool b) := by
  aesop (add simp [HAnd.hAnd,FB.and,left_inv,right_inv,toBool,FB.false,FB.true,valid])

lemma or_equiv (a b : ZMod p) (ha : valid a) (hb : valid b) :
  a ||| b = FB.ofBool (toBool a || toBool b) := by
  aesop (add simp [HOr.hOr,FB.or,left_inv,right_inv,toBool,FB.false,FB.true,valid])

lemma not_equiv (a : ZMod p) (ha : valid a) :
  FB.not a = FB.ofBool (not (toBool a)) := by
  aesop (add simp [FB.not,left_inv,right_inv,toBool,FB.false,FB.true,valid])

lemma xor_equiv (a b : ZMod p) (ha : valid a) (hb : valid b) :
  a ^^^ b = FB.ofBool (toBool a ^^ toBool b) := by
  aesop (add simp [HXor.hXor,FB.xor,left_inv,right_inv,toBool,FB.ofBool,FB.false,FB.true,valid])
  grind

def assertBool_spec (f : ZMod p) :
  FB.assertBool f = some () ↔ valid f := by
  aesop (add simp [FB.assertBool,eq0,sub_eq_zero,imp_iff_not_or,valid])

def assertBool_ofBool_eq_some (b:Bool) : FB.assertBool (p:=p) (FB.ofBool b) = some () := by
  aesop (add simp [assertBool_spec,FB.ofBool,valid,FB.true,FB.false])

def assert (b : Bool) : Option Unit :=
  if b then some () else none

lemma assert_equiv (b : FB p) (h : valid b) :
  Lang.FB.assert b = assert (FB.toBool b) := by
  unfold Lang.FB.assert assert
  aesop (add simp [eq0,toBool,FB.not,FB.false,FB.true,FB.valid])

def conditionallyAssert (a b : Bool) : Option Unit :=
  if a then assert b else some ()

lemma conditionallyAssert_equiv (a b : FB p) (h : valid a) (h : valid b) :
  Lang.FB.conditionallyAssert a b = conditionallyAssert (FB.toBool a) (FB.toBool b) := by
  unfold Lang.FB.conditionallyAssert conditionallyAssert
  aesop (add simp [eq0,toBool,HAnd.hAnd,FB.and,FB.not,FB.false,FB.true,FB.valid])

end Spec.FB

namespace F

def lessThan (w : ℕ) (a b : F p) : Option (FB p) := do
  let d := a - b + 2^w
  let d ← num2bits (w + 1) d
  return FB.not d[w]!

def lessEqThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w a (b + 1)

def greaterThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w b a

def greaterEqThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w b (a + 1)

end F

namespace Spec.F

lemma isZero_def (e:F p) :
  isZero e = some (if e = 0 then 1 else 0) := by
  aesop (add simp [isZero])

private lemma num2bitsLsbPureV_aux_toList_eq {p : ℕ} (w : ℕ) (v : ZMod p) :
    (num2bitsLsbPureV.aux w v).toList = (num2bitsLsbPure w v).reverse := by
  induction w generalizing v with
  | zero => simp [num2bitsLsbPureV.aux, num2bitsLsbPure]
  | succ w ih =>
    simp only [num2bitsLsbPureV.aux, num2bitsLsbPure, Vector.toList_push, List.reverse_cons, ih]

private lemma num2bitsLsbPureV_toList_eq {p : ℕ} (w : ℕ) (v : ZMod p) :
    (num2bitsLsbPureV w v).toList = num2bitsLsbPure w v := by
  simp [num2bitsLsbPureV, Vector.toList_reverse, num2bitsLsbPureV_aux_toList_eq]

-- The i-th bit of the LSB-first representation of f is (f.val / 2^i) % 2
private lemma num2bitsLsbPure_getElem_val {p : ℕ} [NeZero p] (f : ZMod p)
    (n i : ℕ) (hi : i < n) :
    (num2bitsLsbPure n f)[i]'(num2bitsLsbPure_length ▸ hi) =
    ((f.val / 2^i % 2 : ℕ) : ZMod p) := by
  induction n generalizing f i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [num2bitsLsbPure]
    cases i with
    | zero => simp
    | succ i' =>
      have hi' : i' < n := Nat.lt_of_succ_lt_succ hi
      simp only [List.getElem_cons_succ]
      have hrem : ((f.val / 2 : ℕ) : ZMod p).val = f.val / 2 :=
        ZMod.val_cast_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt f))
      rw [ih ((f.val / 2 : ℕ) : ZMod p) i' hi', hrem, pow_succ,
          show 2 ^ i' * 2 = 2 * 2 ^ i' from mul_comm _ _, ← Nat.div_div_eq_div_mul]

private lemma num2bitsLsbPureV_getElem_val {p : ℕ} [NeZero p] (f : ZMod p)
    (w i : ℕ) (hi : i < w) :
    (num2bitsLsbPureV w f)[i]'hi = ((f.val / 2^i % 2 : ℕ) : ZMod p) := by
  have hval := num2bitsLsbPureV_toList_eq w f
  have hlen : i < (num2bitsLsbPureV w f).toList.length := Vector.length_toList ▸ hi
  calc (num2bitsLsbPureV w f)[i]'hi
      = (num2bitsLsbPureV w f).toList[i]'hlen := (Vector.getElem_toList hlen).symm
    _ = (num2bitsLsbPure w f)[i]'(hval ▸ hlen) := List.getElem_of_eq hval hlen
    _ = ((f.val / 2^i % 2 : ℕ) : ZMod p) := num2bitsLsbPure_getElem_val f w i hi

/-
requires:
- a and b ∈ [0,2^w-1]
- w+1 < p

case a < b
then a-b ∈ [-(2^w-1),-1]
then a-b+2^w ∈ [1,2^w-1]
which fits in w bits, so when converted to a (w+1)-bit number, its MSB is 0

case a ≥ b
then a-b ∈ [0,2^w-1]
then a-b+2^w ∈ [2^w,2^(w+1)-1]
which does not fit in w bits, so when converted to a (w+1)-bit number, its MSB is 1
-/
def lessThan_equiv [Fact (Nat.Prime p)] {w} (a b : F p)
    (ha : a.val < 2^w)
    (hb : b.val < 2^w)
    (hw : 2^(w+1) < p) :
    F.lessThan w a b = some (FB.ofBool (a.val < b.val)) := by
  have hp : p ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.Prime.pos Fact.out)
  haveI : NeZero p := ⟨hp⟩
  have h2w_lt_p : 2^w < p :=
    lt_trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self w)) hw
  have h2w_val : (2^w : ZMod p).val = 2^w := by
    have : (2^w : ZMod p) = ((2^w : ℕ) : ZMod p) := by norm_cast
    rw [this]; exact ZMod.val_cast_of_lt h2w_lt_p
  have h_a_plus_2w : (a + (2^w : ZMod p)).val = a.val + 2^w := by
    have h := ZMod.val_add_of_lt (a := a) (b := (2^w : ZMod p)) (by rw [h2w_val]; omega)
    rw [h2w_val] at h; exact h
  have hd_val : (a - b + (2^w : ZMod p)).val = a.val + 2^w - b.val := by
    have heq : a - b + (2^w : ZMod p) = a + (2^w : ZMod p) - b := by ring
    rw [heq, ZMod.val_sub (by rw [h_a_plus_2w]; omega), h_a_plus_2w]
  have hd_lt : (a - b + (2^w : ZMod p)).val < 2^(w+1) := by
    rw [hd_val]
    have h : 2^(w+1) = 2^w + 2^w := by ring
    omega
  have hnum2bits : num2bits (w+1) (a - b + (2^w : ZMod p)) =
      some (num2bitsLsbPureV (w+1) (a - b + (2^w : ZMod p))) := by
    unfold num2bits; simp [hd_lt]
  unfold F.lessThan
  show Option.bind (num2bits (w+1) (a - b + 2^w)) (fun d => some (FB.not d[w]!)) =
       some (FB.ofBool (a.val < b.val))
  rw [hnum2bits, Option.bind_some]
  rw [getElem!_pos (num2bitsLsbPureV (w+1) (a - b + (2^w : ZMod p))) w (Nat.lt_succ_self w),
      num2bitsLsbPureV_getElem_val (a - b + (2^w : ZMod p)) (w+1) w (Nat.lt_succ_self w)]
  by_cases hab : a.val < b.val
  · have hzero : (a - b + (2^w : ZMod p)).val / 2^w = 0 :=
      Nat.div_eq_of_lt (by rw [hd_val]; omega)
    simp [hzero, FB.not, FB.ofBool, FB.true,
          show (decide (a.val < b.val) : Bool) = true from decide_eq_true_eq.mpr hab]
  · push_neg at hab
    have hone : (a - b + (2^w : ZMod p)).val / 2^w = 1 := by
      apply Nat.div_eq_of_lt_le
      · simp; rw [hd_val]; omega
      · rw [hd_val]
        have h : 2 * 2^w = 2^(w+1) := by ring
        omega
    simp [hone, FB.not, FB.ofBool, FB.false,
          show (decide (a.val < b.val) : Bool) = false from
            decide_eq_false_iff_not.mpr (Nat.not_lt.mpr hab)]

end Spec.F


abbrev F8 := F

namespace F8

def ofUInt8 (u:UInt8) : F8 p := UInt8.toFin u

def ofChar (c:Char) : F8 p := ofUInt8 c.toUInt8

def validate (x : F8 p) : Option Unit := do
  let _ ← num2bits 8 x
  ()

abbrev eq (a b : F8 p) := F.eq a b

def lessThan (a b : F8 p) : Option (FB p) := do
  F.lessThan 8 a b

def greaterThan (a b : F8 p) : Option (FB p) :=
  lessThan b a

end F8

namespace Spec.F8

def valid (x: F p) : Prop := x.val < 2^8

def toUInt8 (f:F8 p) : UInt8 := UInt8.ofNat f.val

private lemma ofUInt8_toUInt8 [NeZero p] (u : UInt8) (hp : 2^8 < p) :
    Spec.F8.toUInt8 (F8.ofUInt8 (p := p) u) = u := by
  unfold F8.ofUInt8 Spec.F8.toUInt8
  show UInt8.ofNat ((((UInt8.toFin u).val : ℕ) : ZMod p).val) = u
  rw [ZMod.val_natCast]
  have h_toFin : (UInt8.toFin u).val = u.toNat := rfl
  have hu : u.toNat < 256 := u.toNat_lt
  have h_lt_p : (UInt8.toFin u).val < p := by rw [h_toFin]; omega
  rw [Nat.mod_eq_of_lt h_lt_p]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', h_toFin]
  exact Nat.mod_eq_of_lt hu

private lemma Char.toUInt8_ofUInt8 (n : UInt8) : Char.toUInt8 (Char.ofUInt8 n) = n := by
  show (Char.ofUInt8 n).val.toUInt8 = n
  show n.toUInt32.toUInt8 = n
  exact UInt8.toUInt8_toUInt32 n

private lemma Char.ofUInt8_toUInt8 {c : Char} (hc : c.toNat < 256) :
    Char.ofUInt8 (Char.toUInt8 c) = c := by
  apply Char.ext
  apply UInt32.toNat.inj
  show (Char.toUInt8 c).toUInt32.toNat = c.val.toNat
  rw [UInt8.toNat_toUInt32]
  show (c.val).toUInt8.toNat = c.val.toNat
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt hc

def toChar (c:F8 p) : Char := Char.ofUInt8 (F8.toUInt8 c)

private lemma ofChar_toChar [NeZero p] {f : F p} (h : f.val < 2^8) :
    F8.ofChar (F8.toChar f) = f := by
  unfold F8.ofChar F8.toChar
  rw [Char.toUInt8_ofUInt8]
  show ((Spec.F8.toUInt8 f).toFin.val : ZMod p) = f
  unfold Spec.F8.toUInt8
  rw [UInt8.toFin.ofNat]
  show ((f.val % 256 : ℕ) : ZMod p) = f
  have h256 : f.val < 256 := by
    have : (2:ℕ)^8 = 256 := by norm_num
    omega
  rw [Nat.mod_eq_of_lt h256, ZMod.natCast_zmod_val]

private lemma toChar_ofChar [NeZero p] {c : Char}
    (hc : c.toNat < 256) (hp : 2^8 < p) :
    F8.toChar (F8.ofChar (p:=p) c) = c := by
  unfold F8.ofChar F8.toChar
  rw [ofUInt8_toUInt8 _ hp]
  exact Char.ofUInt8_toUInt8 hc

lemma num2bits_some (x : F p) w :
  (∃ v, num2bits w x = some v) ↔ x.val < 2^w := by
  constructor
  . unfold num2bits
    split
    . aesop
    . aesop
  . intro
    unfold num2bits
    aesop

def validate_valid (x : F p) :
  F8.validate x = some () ↔ valid x := by
  aesop (add simp [F8.validate,Option.bind_eq_some_iff,num2bits_some])

def lessThan_equiv [Fact (Nat.Prime p)] (a b : F p)
    (ha : valid a)
    (hb : valid b)
    (hw : 2^(8+1) < p) :
    F8.lessThan a b = some (FB.ofBool (toUInt8 a < toUInt8 b)) := by
  unfold F8.lessThan
  aesop (add simp [F8.lessThan,F.lessThan_equiv,toUInt8,valid, UInt8.lt_iff_toNat_lt, Nat.mod_eq_of_lt])

end Spec.F8


/-- LSB first, like the output of num2bits -/
abbrev FBitVec (p w : ℕ) := Vector (FB p) w

namespace FBitVec

def default (w:ℕ) : FBitVec p w := Vector.replicate w FB.false

def ofBV {w} (bv : BitVec w) : FBitVec p w :=
  let bv : Fin (2^w) := bv.toFin
  num2bitsLsbPureV w bv

abbrev ofF (w:ℕ) (e:ZMod p) : Option (FBitVec p w) := num2bits w e

abbrev toF {w} (v:FBitVec p w) : ZMod p := bits2numV v

def binSum {w} (a b : FBitVec p w) : Option (FBitVec p (w+1)) :=
  let sum : F p := a.toF + b.toF
  num2bits (w + 1) sum

def assert_eq {w} (a b : FBitVec p w) : Option Unit :=
  (a.zip b).foldlM (fun () (a,b) ↦ FB.assert_eq a b) ()

def eq {w} (a b : FBitVec p w) : Option (FB p) :=
  (a.zip b).foldlM (fun acc (a,b) => do FB.and acc (←FB.eq a b)) FB.true

end FBitVec

namespace Spec.FBitVec

variable [Fact (Nat.Prime p)]

-- We could model FBitVec as sequences of Bools like here, or as Fin like below.

-- def BitVec.ofBoolVecLE {w} (bv : Vector Bool w) : BitVec w :=
--   have h : bv.toArray.toList.length = w := by grind
--   h ▸ BitVec.ofBoolListLE bv.toArray.toList

-- def BitVec.toBoolVecLE {w} (bv : BitVec w) : Vector Bool w := sorry

-- lemma BitVec.right_inv {w} (bv : Vector Bool w) : BitVec.toBoolVecLE (BitVec.ofBoolVecLE bv) = bv := sorry

-- lemma BitVec.left_inv {w} (bv : BitVec w) : BitVec.ofBoolVecLE (BitVec.toBoolVecLE bv) = bv := sorry

-- def boolVecEquiv {w}:
--   Equiv (BitVec w) (Vector Bool w) where
--   toFun := BitVec.toBoolVecLE
--   invFun := BitVec.ofBoolVecLE
--   left_inv := BitVec.left_inv
--   right_inv := BitVec.right_inv

-- def toBV {w} (fbv : FBitVec p w) : BitVec w :=
--   let fbv := fbv.map Spec.FB.toBool
--   BitVec.ofBoolVecLE fbv

-- def ofBV {w} (bv : BitVec w) : FBitVec p w :=
--   let bv : Vector Bool w := BitVec.toBoolVecLE bv
--   bv.map Spec.FB.ofBool

@[aesop safe cases]
def valid {w} (fbv : FBitVec p w) : Prop :=
  (∀ i : Fin w, Spec.FB.valid fbv[i]) ∧
  (2 ^ w < p)

lemma valid_ofBV {w} (bv : BitVec w) :
  valid (FBitVec.ofBV (p:=p) bv) := sorry

def toBV [NeZero p] {w} (fbv : FBitVec p w) : BitVec w :=
  let res := (bits2numV fbv).val % (2^w)
  BitVec.ofFin ⟨res, by aesop (add safe [Nat.mod_lt])⟩

lemma num2bits_equiv {w e} :
  num2bits (p:=p) w e = if h : e.val < 2^w then some (FBitVec.ofBV (BitVec.ofFin ⟨e.val, h⟩)) else none := by
  unfold num2bits FBitVec.ofBV
  split
  simp
  simp

private lemma bits2numV_eq_bits2num {w} (bv : Vector (ZMod p) w) :
    bits2numV bv = bits2num bv.toList := by
  simp only [bits2numV, bits2num, Vector.foldr, Vector.toList, ← Array.foldr_toList]

private lemma num2bitsLsbPureV_aux_toList {w} (v : ZMod p) :
    (num2bitsLsbPureV.aux w v).toList = (num2bitsLsbPure w v).reverse := by
  induction w generalizing v with
  | zero => simp [num2bitsLsbPureV.aux, num2bitsLsbPure]
  | succ w ih =>
    simp only [num2bitsLsbPureV.aux, num2bitsLsbPure, Vector.toList_push, List.reverse_cons, ih]

private lemma num2bitsLsbPureV_toList {w} (v : ZMod p) :
    (num2bitsLsbPureV w v).toList = num2bitsLsbPure w v := by
  simp [num2bitsLsbPureV, Vector.toList_reverse, num2bitsLsbPureV_aux_toList]

private lemma valid_list {w} {bv : FBitVec p w} (hvalid : ∀ i : Fin w, Spec.FB.valid bv[i]) :
    ∀ i : Fin bv.toList.length, bv.toList[i] = 0 ∨ bv.toList[i] = 1 := by
  intro i
  have hi : i.val < w := i.isLt.trans_eq Vector.length_toList
  have hv := hvalid ⟨i.val, hi⟩
  simp only [Spec.FB.valid, FB.false, FB.true] at hv
  rw [Fin.getElem_fin _ _ i.isLt, Vector.getElem_toList i.isLt]
  exact hv

--- also proved in Clap.bits2num_bound for lists
lemma bits2num_bound {w} {bv : FBitVec p w} :
    valid bv → (bits2numV bv).val < 2 ^ w := by
  intro ⟨hvalid, hpow⟩
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [bits2numV, Vector.eq_empty, Vector.foldr]
  · haveI : Fact (2 < p) := ⟨by
        calc 2 = 2^1 := by norm_num
             _ ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hw
             _ < p := hpow⟩
    rw [bits2numV_eq_bits2num]
    have hlen : bv.toList.length = w := Vector.length_toList
    have key := Clap.bits2num_bound (valid_list hvalid)
    rwa [hlen] at key

lemma bits2num_equiv {w} {bv : FBitVec p w} {h : valid bv} :
  bits2numV bv = BitVec.toFin (toBV bv) := by
  unfold toBV
  simp
  have h : 2^w ≠ 0 := by grind
  have h : (bits2numV bv).val < 2^w → (bits2numV bv).val % 2^w = (bits2numV bv).val := (Nat.mod_eq_iff_lt h).mpr
  rw [h]
  . aesop (add simp [eq_comm, ZMod.natCast_zmod_val])
  . aesop (add safe [bits2num_bound])

--- also proved in Clap.num2bitsLsbPure_of_bits2num_eq for list
lemma num2bitsLsbPure_of_bits2num_eq {w} {fbv : FBitVec p w}
  (h: valid fbv) :
num2bitsLsbPureV w (bits2numV fbv) = fbv := by
  apply Vector.toList_inj.mp
  rw [num2bitsLsbPureV_toList, bits2numV_eq_bits2num]
  have hlen : fbv.toList.length = w := Vector.length_toList
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Vector.eq_empty, num2bitsLsbPure]
  · haveI : Fact (2 < p) := ⟨by
        calc 2 = 2^1 := by norm_num
             _ ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hw
             _ < p := h.2⟩
    have key := Clap.num2bitsLsbPure_of_bits2num_eq (by rw [hlen]; exact h.2) (valid_list h.1)
    rwa [hlen] at key

--- also proved in Clap.bits2num_of_num2bitsLsbPure_eq for list
lemma bits2num_of_num2bitsLsbPure_eq {w : ℕ} {v : F p} :
  v.val < 2 ^ w → bits2numV (num2bitsLsbPureV w v) = v := by
  rw [bits2numV_eq_bits2num, num2bitsLsbPureV_toList]
  revert v
  induction w with
  | zero =>
    intro v h
    simp only [pow_zero, Nat.lt_one_iff, ZMod.val_eq_zero] at h
    simp [h, num2bitsLsbPure, bits2num]
  | succ w ih =>
    intro v h
    unfold num2bitsLsbPure bits2num
    simp only [List.foldr_cons]
    unfold bits2num at ih
    have h' : (((v.val / 2) : ℕ) : ZMod p).val < 2 ^ w := by
      simp only [ZMod.val_natCast]
      exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.nat_repr_len_aux v.val 2 w (by decide) h)
    rw [ih h']
    conv_rhs => rw [← ZMod.natCast_zmod_val v, ← Nat.mod_add_div v.val 2]
    simp [Nat.cast_add, Nat.cast_mul]

def left_inv {w} (fbv : FBitVec p w) (h : valid fbv) :
  FBitVec.ofBV (toBV fbv) = fbv := by
  aesop (add simp [FBitVec.ofBV,toBV,num2bitsLsbPure_of_bits2num_eq,bits2num_bound,Nat.mod_eq_of_lt])

def right_inv {w} (bv : BitVec w) (h: 2^w < p) :
  toBV (p:=p) (FBitVec.ofBV bv) = bv := by
  have hlt : bv.toNat < p := lt_trans bv.isLt h
  have hv : (bv.toNat : ZMod p).val < 2 ^ w := by
    rw [ZMod.val_natCast_of_lt hlt]; exact bv.isLt
  have hbits : bits2numV (num2bitsLsbPureV w (bv.toNat : ZMod p)) = (bv.toNat : ZMod p) := by
    rw [bits2num_of_num2bitsLsbPure_eq]
    assumption
  apply BitVec.toNat_inj.mp
  unfold toBV FBitVec.ofBV
  simp only [BitVec.toNat_ofFin]
  change (bits2numV (num2bitsLsbPureV w (bv.toNat : ZMod p))).val % 2^w = bv.toNat
  rw [hbits, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt bv.isLt]

lemma eq_equiv {w} (a b : FBitVec p w) (ha : valid a) (hb : valid b) :
  FBitVec.eq a b = some (FB.ofBool ((toBV a) = (toBV b))) := by
  aesop (add simp [FBitVec.eq,FBitVec.toBV])
  sorry

end Spec.FBitVec


structure PaddedVector (α : ℕ → Type) (p w : ℕ) where
  data : Vector (α p) w
  len : F p

abbrev FString (p maxLen : ℕ) := PaddedVector F8 p maxLen

namespace FString

def ofString {w:ℕ} (s:String) : FString p w :=
  let l := s.toList.map (F8.ofChar (p:=p))
  let a := l.toArray.toVector
  if h : a.size < w
  then
    have h : l.toArray.size + (w - a.size) = w := by grind
    let data := h ▸ (a ++ Vector.replicate (w - a.size) (0:F p))
    {data, len := a.size}
  else
    let h : min w l.toArray.size = w := by grind
    let data := h ▸ a.take w
    {data, len := w}

def isPaddedOf {wa} (a : FString p wa) (b : String) : Option (FB p) := do
  let b : List (F8 p) := b.toList.map F8.ofChar
  (← aux a.data.toArray.toList b)
  &&&
  (← F.eq a.len b.length)
where
  aux : List (F p) → List (F p) → Option (FB p)
  | x :: xs, y :: ys => return (←F.eq x y) &&& (← aux xs ys)
  | _, _ => return 1

end FString

namespace Spec.FString

def toString {w:ℕ} (fs : FString p w) : String :=
  let v := fs.data.take fs.len.val
  String.ofList (v.toArray.toList.map F8.toChar)

def valid {w} (fs : FString p w) : Prop :=
  (∀ i : Fin w, F8.valid fs.data[i]) ∧ fs.len.val < w ∧
  (∀ i : Fin w, fs.len.val ≤ i.val → fs.data[i] = 0)

private theorem eqRec_toList {α} {n m : ℕ} (h : n = m) (v : Vector α n) :
    (h ▸ v).toList = v.toList := by
  cases h; rfl

def ofString_toString {w} [NeZero p] (fs : FString p w) (h : valid fs) :
    FString.ofString (toString fs) = fs := by
  obtain ⟨hvalid, hlen, hpad⟩ := h
  rcases fs with ⟨data, len⟩
  simp only at hlen hvalid hpad
  -- Per-element F8↔Char round trip
  have hmap : ∀ i : Fin w, F8.ofChar (F8.toChar data[i]) = data[i] :=
    fun i => F8.ofChar_toChar (hvalid i)
  -- Zero-padding consequence as a List equality
  have hdrop : data.toList.drop len.val = List.replicate (w - len.val) 0 := by
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      have hlen_drop : i < w - len.val := by
        simpa [List.length_drop, Vector.length_toList] using hi₁
      have hi_lt_w : len.val + i < w := by omega
      simp only [List.get_eq_getElem, List.getElem_drop, List.getElem_replicate,
                 Vector.getElem_toList]
      exact hpad ⟨len.val + i, hi_lt_w⟩ (Nat.le_add_right len.val i)
  -- The mapped list equals data.toList.take len.val
  have hlist : (toString { data := data, len := len : FString p w}).toList.map
                  (F8.ofChar (p := p)) = data.toList.take len.val := by
    unfold toString
    rw [String.toList_ofList, List.map_map, Vector.toList_toArray, Vector.toList_take]
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      have hi_lt_take : i < min len.val w := by
        simpa [List.length_take, Vector.length_toList] using hi₂
      have hi_lt_w : i < w := by omega
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_take, Function.comp_apply,
                 Vector.getElem_toList]
      exact hmap ⟨i, hi_lt_w⟩
  -- Length and size of the mapped list = len.val
  have hLlen : ((toString { data := data, len := len : FString p w}).toList.map
                  (F8.ofChar (p := p))).length = len.val := by
    rw [hlist, List.length_take, Vector.length_toList, min_eq_left hlen.le]
  have hLsize : ((toString { data := data, len := len : FString p w}).toList.map
                  (F8.ofChar (p := p))).toArray.size = len.val := by
    rw [List.size_toArray]; exact hLlen
  show FString.ofString (toString { data := data, len := len : FString p w}) =
       { data := data, len := len }
  unfold FString.ofString
  -- The if condition is true since len.val < w
  have hcond : (((toString { data := data, len := len : FString p w}).toList.map
                  (F8.ofChar (p := p))).toArray.toVector.size < w) := by
    change (((toString { data := data, len := len : FString p w}).toList.map _).toArray.size < w)
    omega
  rw [dif_pos hcond]
  -- Goal: { data := h ▸ (a ++ Vector.replicate (w - a.size) 0), len := ↑a.size } = { data, len }
  refine PaddedVector.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · -- data equality
    apply Vector.toList_inj.mp
    rw [eqRec_toList, Vector.toList_append, Vector.toList_replicate]
    change ((toString { data := data, len := len : FString p w}).toList.map
              (F8.ofChar (p := p))).toArray.toList ++
           List.replicate (w - ((toString { data := data, len := len : FString p w}).toList.map
                                  (F8.ofChar (p := p))).toArray.size) 0
           = data.toList
    rw [hLsize, List.toList_toArray, hlist, ← hdrop, List.take_append_drop]
  · -- len equality: (↑a.size : F p) = len, with a.size = len.val
    change ((((toString { data := data, len := len : FString p w}).toList.map
              (F8.ofChar (p := p))).toArray.size : ℕ) : F p) = len
    rw [hLsize]
    exact ZMod.natCast_zmod_val len

def toString_ofString {w} [NeZero p] (s : String) (hlen : s.length ≤ w)
    (hchars : ∀ c ∈ s.toList, c.toNat < 256) (hp : 2^8 < p) (hpw : w < p) :
    toString (p:=p) (FString.ofString (w:=w) s) = s := by
  -- The mapped list has length s.length
  have hL_length : (s.toList.map (F8.ofChar (p := p))).length = s.length := by
    rw [List.length_map, String.length_toList]
  have hLsize : (s.toList.map (F8.ofChar (p := p))).toArray.size = s.length := by
    rw [List.size_toArray]; exact hL_length
  -- Final character-level identity used in both branches
  have hroundtrip : ∀ c ∈ s.toList,
      F8.toChar (F8.ofChar (p := p) c) = c :=
    fun c hc => F8.toChar_ofChar (hchars c hc) hp
  have hmap_eq : (s.toList.map (F8.ofChar (p := p))).map F8.toChar = s.toList := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id s.toList]
    apply List.map_congr_left
    intro c hc
    exact hroundtrip c hc
  show toString (FString.ofString (p := p) (w := w) s) = s
  unfold FString.ofString
  by_cases hsize : s.length < w
  · -- if-then branch: data := h ▸ (a ++ replicate (w - a.size) 0), len := ↑a.size
    have hcond : ((s.toList.map (F8.ofChar (p := p))).toArray.toVector.size < w) := by
      change ((s.toList.map (F8.ofChar (p := p))).toArray.size < w)
      omega
    rw [dif_pos hcond]
    unfold toString
    apply String.toList_inj.mp
    rw [String.toList_ofList]
    -- a.size = s.length, len = (s.length : F p), len.val = s.length
    have hsize_eq : ((s.toList.map (F8.ofChar (p := p))).toArray.toVector.size : ℕ) = s.length := hLsize
    have h_lenval : ((((s.toList.map (F8.ofChar (p := p))).toArray.toVector.size : ℕ) : F p).val) = s.length := by
      rw [hsize_eq, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt hlen hpw)]
    rw [h_lenval]
    rw [Vector.toList_toArray, Vector.toList_take, eqRec_toList,
        Vector.toList_append, Vector.toList_replicate]
    change List.map F8.toChar
             (List.take s.length
                ((s.toList.map (F8.ofChar (p := p))).toArray.toList ++
                 List.replicate (w - (s.toList.map (F8.ofChar (p := p))).toArray.size) 0))
             = s.toList
    rw [List.toList_toArray]
    -- Goal: List.map F8.toChar ((mapped ++ List.replicate ... 0).take s.length) = s.toList
    rw [List.take_append_of_le_length (le_of_eq hL_length.symm)]
    rw [List.take_of_length_le (le_of_eq hL_length)]
    exact hmap_eq
  · -- else branch: data := h ▸ a.take w, len := ↑w; combined with hlen gives s.length = w
    push_neg at hsize
    have heq : s.length = w := le_antisymm hlen hsize
    have hcond : ¬ ((s.toList.map (F8.ofChar (p := p))).toArray.toVector.size < w) := by
      change ¬ ((s.toList.map (F8.ofChar (p := p))).toArray.size < w)
      omega
    rw [dif_neg hcond]
    unfold toString
    apply String.toList_inj.mp
    rw [String.toList_ofList]
    have h_lenval : ((w : ℕ) : F p).val = w := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hpw]
    rw [h_lenval]
    rw [Vector.toList_toArray, Vector.toList_take, eqRec_toList, Vector.toList_take]
    change List.map F8.toChar
             (List.take w
                ((s.toList.map (F8.ofChar (p := p))).toArray.toList.take w))
           = s.toList
    rw [List.toList_toArray]
    -- Goal: List.map F8.toChar ((mapped.take w).take w) = s.toList
    rw [List.take_take, min_self]
    rw [List.take_of_length_le (by rw [hL_length]; omega)]
    exact hmap_eq

private lemma isPaddedOf_aux_eq (as bs : List (F p)) :
    FString.isPaddedOf.aux as bs =
      some (FB.ofBool ((as.zip bs).all (fun q => decide (q.1 = q.2)))) := by
  induction as generalizing bs with
  | nil => simp [FString.isPaddedOf.aux, FB.ofBool, FB.true]
  | cons x xs ih =>
    cases bs with
    | nil => simp [FString.isPaddedOf.aux, FB.ofBool, FB.true]
    | cons y ys =>
      show (do let e ← F.eq x y; let r ← FString.isPaddedOf.aux xs ys; pure (e &&& r))
              = some (FB.ofBool _)
      rw [F.eq, F.isZero_def, ih]
      simp only [sub_eq_zero, List.zip_cons_cons, List.all_cons]
      simp only [bind, Option.bind]
      by_cases hxy : x = y
      · simp only [hxy, decide_true, Bool.true_and, if_true, pure, HAnd.hAnd, FB.and, one_mul]
      · simp [hxy, FB.ofBool, FB.false, FB.and, HAnd.hAnd]

lemma isPaddedOf_equiv {w} [NeZero p] (fs : FString p w) (s : String)
    (hf : valid fs)
    (hchars : ∀ c ∈ s.toList, c.toNat < 256)
    (hp : 2^8 < p) (hps : s.length < p) :
    fs.isPaddedOf s = FB.ofBool (p:=p) (toString fs = s) := by
  obtain ⟨hvalid, hlen, hpad⟩ := hf
  rcases fs with ⟨data, len⟩
  simp only at hvalid hlen hpad
  -- shortcuts
  set b : List (F p) := s.toList.map F8.ofChar with hb_def
  have hb_length : b.length = s.length := by simp [hb_def, String.length_toList]
  set as : List (F p) := data.toArray.toList with has_def
  have has_length : as.length = w := by
    rw [has_def, Array.length_toList, Vector.size_toArray]
  unfold FString.isPaddedOf
  simp only [hb_def.symm, has_def.symm]
  rw [isPaddedOf_aux_eq, F.eq, F.isZero_def]
  simp only [bind, Option.bind, sub_eq_zero]
  -- Now combine the FB.ofBool's
  have hand : ∀ (P Q : Bool), (FB.ofBool (p:=p) P) &&& (FB.ofBool (p:=p) Q) =
      FB.ofBool (P && Q) := by
    intros P Q
    cases P <;> cases Q <;>
      simp [FB.ofBool, FB.true, FB.false, FB.and, HAnd.hAnd]
  -- Express the F.eq result as FB.ofBool
  have h_len_eq : (if len = (↑b.length : F p) then (1 : FB p) else 0) =
      FB.ofBool (decide (len = (↑b.length : F p))) := by
    by_cases h : len = (↑b.length : F p)
    · simp [h, FB.ofBool, FB.true]
    · simp [h, FB.ofBool, FB.false]
  rw [h_len_eq, hand]
  -- Goal: some (FB.ofBool (P && Q)) = some (FB.ofBool (toString fs = s))
  congr 1
  congr 1
  -- ((as.zip b).all ... && decide (len = ↑b.length)) = decide (toString fs = s)
  -- Helper: len = ↑b.length in F p ↔ len.val = s.length
  have h_len_iff : (len = (↑b.length : F p)) ↔ (len.val = s.length) := by
    rw [hb_length]
    constructor
    · intro h
      have hval : len.val = ((s.length : ℕ) : F p).val := by rw [h]
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hps] at hval
    · intro h
      conv_lhs => rw [← ZMod.natCast_zmod_val len]
      rw [h]
  -- Helper: toString = s ↔ list equality
  have h_toStr_iff : toString { data := data, len := len : FString p w } = s ↔
      (data.toList.take len.val).map F8.toChar = s.toList := by
    unfold toString
    simp only [Vector.toList_toArray, Vector.toList_take]
    rw [← String.toList_inj, String.toList_ofList]
  -- Helper: b[i] = F8.ofChar s.toList[i]
  have h_b_get : ∀ i (hi : i < s.toList.length),
      b[i]'(by rw [hb_length, ← String.length_toList]; exact hi) =
        F8.ofChar (s.toList[i]'hi) := by
    intro i hi
    show (s.toList.map F8.ofChar)[i]'(by rw [List.length_map]; exact hi) =
        F8.ofChar (s.toList[i]'hi)
    exact List.getElem_map _
  -- Helper: data round trip
  have h_data_val : ∀ i (hi : i < w),
      F8.ofChar (F8.toChar (data[i]'hi)) = data[i]'hi :=
    fun i hi => F8.ofChar_toChar (hvalid ⟨i, hi⟩)
  -- Helper: as[i] = data[i]
  have h_as_data : ∀ i (hi : i < w),
      as[i]'(by rw [has_length]; exact hi) = data[i]'hi := by
    intro i hi
    show data.toArray.toList[i]'(by rw [Array.length_toList, Vector.size_toArray]; exact hi)
      = data[i]'hi
    rw [Array.getElem_toList, Vector.getElem_toArray]
  -- Now case-split on toString = s
  by_cases htoStr : toString { data := data, len := len : FString p w } = s
  · -- toString = s: show LHS bool = true
    rw [decide_eq_true htoStr]
    rw [h_toStr_iff] at htoStr
    have hL_len : (List.map F8.toChar (data.toList.take len.val)).length = s.toList.length := by
      rw [htoStr]
    rw [List.length_map, List.length_take, Vector.length_toList,
        String.length_toList, min_eq_left hlen.le] at hL_len
    -- hL_len : len.val = s.length
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- all elements match
      rw [List.all_eq_true]
      intro q hq
      rw [decide_eq_true_eq]
      rcases List.mem_iff_getElem.mp hq with ⟨n, hn_lt, hn_eq⟩
      rw [List.getElem_zip] at hn_eq
      subst hn_eq
      simp only
      have hn_lt_zip : n < (as.zip b).length := hn_lt
      rw [List.length_zip] at hn_lt_zip
      have hn_lt_as : n < as.length := lt_of_lt_of_le hn_lt_zip (min_le_left _ _)
      have hn_lt_b : n < b.length := lt_of_lt_of_le hn_lt_zip (min_le_right _ _)
      have hn_lt_w : n < w := has_length ▸ hn_lt_as
      have hn_lt_slen : n < s.length := hb_length ▸ hn_lt_b
      have hn_lt_sl : n < s.toList.length := by rw [String.length_toList]; exact hn_lt_slen
      have hn_lt_lv : n < len.val := by omega
      rw [h_as_data n hn_lt_w, h_b_get n hn_lt_sl]
      have hi_mapped : n < ((data.toList.take len.val).map F8.toChar).length := by
        rw [List.length_map, List.length_take, Vector.length_toList,
            min_eq_left hlen.le]; exact hn_lt_lv
      have h_at_n := List.getElem_of_eq htoStr hi_mapped
      rw [List.getElem_map, List.getElem_take, Vector.getElem_toList] at h_at_n
      have hcombined : F8.ofChar (p:=p) (F8.toChar (data[n]'hn_lt_w)) =
             F8.ofChar (p:=p) (s.toList[n]'hn_lt_sl) := by
        rw [h_at_n]
      rw [h_data_val] at hcombined
      exact hcombined
    · rw [decide_eq_true_eq, h_len_iff]
      exact hL_len
  · -- toString ≠ s: show LHS bool = false
    rw [decide_eq_false htoStr]
    rw [Bool.and_eq_false_iff]
    rw [h_toStr_iff] at htoStr
    by_cases hLen : len.val = s.length
    · -- Case B: lengths match, lists differ at some position
      left
      have h_lengths : ((data.toList.take len.val).map F8.toChar).length = s.toList.length := by
        rw [List.length_map, List.length_take, Vector.length_toList,
            min_eq_left hlen.le, String.length_toList]
        exact hLen
      -- ∃ i where the lists differ
      have h_diff : ∃ i : ℕ, ∃ (hi : i < s.toList.length),
          ((data.toList.take len.val).map F8.toChar)[i]'(by rw [h_lengths]; exact hi) ≠
            s.toList[i] := by
        by_contra hall
        push_neg at hall
        apply htoStr
        apply List.ext_getElem h_lengths
        intro j hj₁ hj₂
        exact hall j hj₂
      obtain ⟨i, hi_slen, hi_neq⟩ := h_diff
      rw [String.length_toList] at hi_slen
      have hi_lv : i < len.val := by
        have := hi_slen
        omega
      have hi_w : i < w := by omega
      -- The pair (as[i], b[i]) is in as.zip b, and they don't match
      have h_zip_len : (as.zip b).length = min as.length b.length := List.length_zip
      have hi_zip : i < (as.zip b).length := by
        rw [h_zip_len, has_length, hb_length]
        omega
      rw [← Bool.not_eq_true]
      rw [List.all_eq_true]
      push_neg
      refine ⟨(as.zip b)[i]'hi_zip, ?_, ?_⟩
      · exact List.getElem_mem hi_zip
      · simp only [ne_eq, decide_eq_true_eq]
        rw [List.getElem_zip]
        simp only
        have hi_sl' : i < s.toList.length := by rw [String.length_toList]; exact hi_slen
        rw [h_as_data i hi_w, h_b_get i hi_sl']
        intro habs
        apply hi_neq
        -- habs : data[i] = F8.ofChar s.toList[i]
        have hi_dat_take : i < (data.toList.take len.val).length := by
          rw [List.length_take, Vector.length_toList, min_eq_left hlen.le]; exact hi_lv
        have hi_dat_map : i < ((data.toList.take len.val).map F8.toChar).length := by
          rw [List.length_map]; exact hi_dat_take
        show ((data.toList.take len.val).map F8.toChar)[i]'hi_dat_map = s.toList[i]'(by
          rw [String.length_toList]; exact hi_slen)
        rw [List.getElem_map, List.getElem_take, Vector.getElem_toList, habs]
        exact F8.toChar_ofChar (hchars _ (s.toList.getElem_mem hi_sl')) hp
    · -- Case A: len.val ≠ s.length, so F.eq returns false
      right
      rw [decide_eq_false_iff_not, h_len_iff]
      exact hLen

end Spec.FString

abbrev FBV8 (p:ℕ) := FBitVec p 8

namespace FBV8

def ofUInt8 (u:UInt8) : FBV8 p :=
  UInt8.toBitVec u |> FBitVec.ofBV

def ofF (x:F p) : Option (FBV8 p) := do
  FBitVec.ofF 8 x

end FBV8

namespace Spec.FBV8

variable [Fact (Nat.Prime p)]

abbrev valid (x:FBV8 p) := FBitVec.valid x

def toUInt8 (x:FBV8 p) : UInt8 :=
  Spec.FBitVec.toBV x |> UInt8.ofBitVec

lemma left_inv (u:UInt8) (h : 2^8 < p):
  FBV8.toUInt8 (FBV8.ofUInt8 (p:=p) u) = u := by
  unfold FBV8.toUInt8 FBV8.ofUInt8
  aesop (add simp [Spec.FBitVec.right_inv])

lemma ofF_equiv (e:ZMod p) :
  FBV8.ofF e = if h : e.val < 2^8 then some (FBV8.ofUInt8 (UInt8.ofFin ⟨e.val,h⟩)) else none := by
  unfold FBV8.ofF FBitVec.ofF
  apply Spec.FBitVec.num2bits_equiv

end Spec.FBV8


abbrev F32 (p:ℕ) := FBitVec p 32

namespace F32

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofUInt32 (u:UInt32) : F32 p :=
  UInt32.toBitVec u |> FBitVec.ofBV

def ofF (x:F p) : Option (F32 p) := do
  FBitVec.ofF 32 x

def ofFBV8 [Fact (Primes.fits p 8)] (u8 : FBV8 p) : F32 p :=
  u8 ++ (Vector.replicate 24 (0:FB p))

def add (a b : F32 p) : Option (F32 p) := do
  have h : Option (FBitVec p (min 32 (32 + 1))) = Option (F32 p) := by grind
  h ▸ Vector.take (← FBitVec.binSum a b) 32

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

namespace Spec.F32

variable [Fact (Nat.Prime p)]

def toUInt32 (x:F32 p) : UInt32 :=
  Spec.FBitVec.toBV x |> UInt32.ofBitVec

lemma add_equiv (a b : F32 p) (ha : Spec.FBitVec.valid a) (hb : Spec.FBitVec.valid b) :
  F32.add a b = some (F32.ofUInt32 (UInt32.add (toUInt32 a) (toUInt32 b))) := by
  unfold F32.add FBitVec.binSum FBitVec.toF
  rw [Spec.FBitVec.bits2num_equiv]
  rw [Spec.FBitVec.bits2num_equiv]
  rw [Spec.FBitVec.num2bits_equiv]
  --simp
  split
  . simp only [toUInt32,F32.ofUInt32]
    by_cases h : (((FBitVec.toBV a).toNat : ZMod p) + ↑(FBitVec.toBV b).toNat).val < 2^32
    . -- simp only [instHAdd, Add.add]
      simp only [Option.bind_eq_bind, Option.bind_some]
      erw [UInt32.toBitVec_add (a:={ toBitVec := FBitVec.toBV a }) (b:={ toBitVec := FBitVec.toBV b })]
      simp only [BitVec.val_toFin]
      have h2: ((FBitVec.toBV a).toNat : ZMod p).val + ((FBitVec.toBV b).toNat : ZMod p).val < p := sorry
      -- erw [ZMod.val_add_of_lt (n:=p) (a:=((FBitVec.toBV a).toNat : ZMod p)) (b:=((FBitVec.toBV b).toNat :ZMod p)) h2]
      sorry
    . sorry
  . sorry -- absurd
  repeat assumption

end Spec.F32


abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] := FBitVec p 64

namespace F64

variable [Fact (Primes.fits p 64)]

def ofF (x:F p) : Option (F64 p) :=
  FBitVec.ofF 64 x

end F64

def FByteArray (p w : ℕ) [Fact (Primes.fits p 8)] := Vector (FBV8 p) w

namespace FByteArray

end FByteArray

end Clap.Lang

namespace Test

abbrev p := Primes.goldilocks

open Clap.Lang

example : F.lessThan 1 (0 : F p) 1 == some 1 := by native_decide
example : F.lessThan 1 (0 : F p) 0 == some 0 := by native_decide
example : F.lessThan 2 (1 : F p) 2 == some 1 := by native_decide
example : F.lessThan 2 (2 : F p) 1 == some 0 := by native_decide
example : F.lessThan 8 (42 : F p) (2^8 - 1) == some 1 := by native_decide
example : F.lessThan 8 (2^8 - 1) (42 : F p) == some 0 := by native_decide

example : F.lessEqThan 2 (2 : F p) 2 == some 1 := by native_decide
example : F.lessEqThan 2 (1 : F p) 2 == some 1 := by native_decide
example : F.lessEqThan 2 (3 : F p) 2 == some 0 := by native_decide

example : F.greaterThan 2 (3 : F p) 2 == some 1 := by native_decide
example : F.greaterThan 2 (2 : F p) 2 == some 0 := by native_decide

example : F.greaterEqThan 2 (3 : F p) 2 == some 1 := by native_decide
example : F.greaterEqThan 2 (2 : F p) 2 == some 1 := by native_decide
example : F.greaterEqThan 2 (2 : F p) 3 == some 0 := by native_decide


def testBinSum (a b : FBitVec p 3) (expected : FBitVec p 4) : Option Unit := do
  FBitVec.assert_eq (← FBitVec.binSum a b) expected

example : (testBinSum #v[1,0,0] #v[1,0,0] #v[0,1,0,0]) = some () := by native_decide
example : (testBinSum #v[0,0,1] #v[0,0,1] #v[0,0,0,1]) = some () := by native_decide
example : (testBinSum #v[1,1,1] #v[1,0,0] #v[0,0,0,1]) = some () := by native_decide

instance : Coe UInt32 (F32 p) where
  coe n := Clap.num2bitsLsbPureV 32 n.toNat

instance (n:ℕ) : OfNat (F32 p) n where
  ofNat := Clap.num2bitsLsbPureV 32 n

example :
  letI a : UInt32 := 2^32 - 1
  (F32.add (a : F32 p) (1 : F32 p)) = ((UInt32.add a 1) : F32 p) := by native_decide

end Test
