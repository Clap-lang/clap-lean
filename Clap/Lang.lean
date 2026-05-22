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

variable {p : ℕ} [Fact (Nat.Prime p)]

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

end FB

namespace Spec.FB

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

def lessThan {w} (a b : FBitVec p w) : Option (FB p) :=
  (a.zip b).foldlM (fun acc (aᵢ, bᵢ) ↦ do
    let eqᵢ ← FB.eq aᵢ bᵢ
    (eqᵢ &&& acc) ||| ((FB.not eqᵢ) &&& (FB.not aᵢ))
  ) FB.false

def greaterThan {w} (a b : FBitVec p w) : Option (FB p) :=
  lessThan b a

end FBitVec

namespace Spec.FBitVec

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

def toBV [NeZero p] {w} (fbv : FBitVec p w) : BitVec w :=
  let res := (bits2numV fbv).val % (2^w)
  BitVec.ofFin ⟨res, by aesop (add safe [Nat.mod_lt])⟩

lemma num2bits_equiv {w e} :
  num2bits (p:=p) w e = if h : e.val < 2^w then some (FBitVec.ofBV (BitVec.ofFin ⟨e.val, h⟩)) else none := by
  unfold num2bits FBitVec.ofBV
  split
  simp
  simp

-- proved in Clap.bits2num_bound
lemma bits2num_bound {w} {bv : FBitVec p w} :
    valid bv → (bits2numV bv).val < 2 ^ w := sorry

lemma bits2num_equiv {w} {bv : FBitVec p w} {h : valid bv} :
  bits2numV bv = BitVec.toFin (toBV bv) := by
  unfold toBV
  simp
  have h : 2^w ≠ 0 := by grind
  have h : (bits2numV bv).val < 2^w → (bits2numV bv).val % 2^w = (bits2numV bv).val := (Nat.mod_eq_iff_lt h).mpr
  rw [h]
  . aesop (add simp [eq_comm, ZMod.natCast_zmod_val])
  . aesop (add safe [bits2num_bound])

-- proved in Clap.num2bitsLsbPure_of_bits2num_eq for list
lemma num2bitsLsbPure_of_bits2num_eq {w} {fbv : FBitVec p w}
  (h: valid fbv) :
num2bitsLsbPureV w (bits2numV fbv) = fbv := sorry

-- proved in Clap.bits2num_of_num2bitsLsbPure_eq for list
lemma bits2num_of_num2bitsLsbPure_eq {w : ℕ} {v : F p} :
  v.val < 2 ^ w → bits2numV (num2bitsLsbPureV w v) = v := by
  sorry

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
def lessThan_equiv {w} (a b : FBitVec p w) :
  FBitVec.lessThan a b = some (FB.ofBool ((toBV a) < (toBV b))) := by
  unfold FBitVec.lessThan
  -- TODO problems with the rewrites
  -- generalize eq : (Vector.zip a b) = l
  -- apply Vector.mk
  -- apply Vector.zip_mk
  -- induction

  -- simp only [Spec.FB.and_equiv, Spec.FB.or_equiv,
  --                  Spec.FB.eq_equiv,
  --                  Spec.FB.not_equiv]
  -- rw [Spec.FB.and_equiv]
  -- rw [Spec.FB.or_equiv]
  -- rw [Spec.FB.eq_equiv]
  -- rw [Spec.FB.not_equiv]

  -- conv =>
  --   enter [1,1,acc,x,3,ai,bi]
  --   rw [Spec.FB.eq_equiv]
  --   rw [Spec.FB.not_equiv]
  --   simp
  --  -- enter [2,eqi]
  --   rw [Spec.FB.and_equiv]
  --   rw [Spec.FB.and_equiv]
  --   rw [Spec.FB.or_equiv]
  --   simp [Spec.FB.left_inv,Spec.FB.right_inv]

  sorry

end Spec.FBitVec


abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] := FBitVec p 8

namespace F8

variable [Fact (Primes.fits p 8)]

def ofUInt8 (u:UInt8) : F8 p :=
  UInt8.toBitVec u |> FBitVec.ofBV

def ofF (x:F p) : Option (F8 p) := do
  FBitVec.ofF 8 x

def eq (a b : F8 p) : Option (FB p) := FBitVec.eq a b

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8

namespace Spec.F8

variable [Fact (Primes.fits p 8)]

abbrev valid (x:F8 p) := FBitVec.valid x

def toUInt8 (x:F8 p) : UInt8 :=
  Spec.FBitVec.toBV x |> UInt8.ofBitVec

lemma left_inv (u:UInt8) (h : 2^8 < p):
  F8.toUInt8 (F8.ofUInt8 (p:=p) u) = u := by
  unfold F8.toUInt8 F8.ofUInt8
  aesop (add simp [Spec.FBitVec.right_inv])

lemma ofF_equiv (e:ZMod p) :
  F8.ofF e = if h : e.val < 2^8 then some (F8.ofUInt8 (UInt8.ofFin ⟨e.val,h⟩)) else none := by
  unfold F8.ofF FBitVec.ofF
  apply Spec.FBitVec.num2bits_equiv

lemma eq_equiv (a b : F8 p) :
  F8.eq a b = some (FB.ofBool ((toUInt8 a) = (toUInt8 b))) := by
  sorry

end Spec.F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] := FBitVec p 32

namespace F32

variable [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofUInt32 (u:UInt32) : F32 p :=
  UInt32.toBitVec u |> FBitVec.ofBV

def ofF (x:F p) : Option (F32 p) := do
  FBitVec.ofF 32 x

def ofF8 [Fact (Primes.fits p 8)] (u8 : F8 p) : F32 p :=
  u8 ++ (Vector.replicate 24 (0:FB p))

def add (a b : F32 p) : Option (F32 p) := do
  have h : Option (FBitVec p (min 32 (32 + 1))) = Option (F32 p) := by grind
  h ▸ Vector.take (← FBitVec.binSum a b) 32

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

namespace Spec.F32

variable [Fact (Primes.fits p 32)]

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

def FByteArray (p w : ℕ) [Fact (Primes.fits p 8)] := Vector (F8 p) w

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

def F8.ofF! {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : F p → F8 p := Clap.num2bitsLsbPureV 8

example : FBitVec.lessThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == some 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == some 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == some 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 42) (F8.ofF! 255) == some 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 255) (F8.ofF! 42) == some 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == some 1 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == some 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == some 0 := by native_decide

end Test
