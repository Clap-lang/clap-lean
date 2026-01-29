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

def addCarry (a b : FU8 p) (carryIn : FB p := 0) : (FU8 p) × (FB p) :=
  Spec.div_rem (a + b + carryIn) |>.swap

abbrev addCarry' := @addCarry prime_babybear

#guard addCarry' 1 1 = (2,0)
#guard addCarry' 255 2 = (1,1)
#guard addCarry' 255 3 = (2,1)
#guard addCarry' 255 255 1 = (255,1)

def mulCarry (a b : FU8 p) (c : ZMod p := 0) : FU8 p × (ZMod p) :=
  Spec.div_rem (a * b + c) |>.swap

abbrev mulCarry' := @mulCarry prime_babybear

#guard mulCarry' 0 0 = (0, 0)
#guard mulCarry' 10 1 = (10, 0)
#guard mulCarry' 1 10 = (10, 0)
#guard mulCarry' 10 0 5 = (5, 0)
#guard mulCarry' 128 2 = (0, 1)
#guard mulCarry' 128 2 1 = (1, 1)
#guard mulCarry' 255 255 = (1, 254)
#guard mulCarry' 255 255 255 = (0, 255)
#guard mulCarry' 16 16 = (0, 1)
#guard mulCarry' 2 100 200 = (144, 1)
#guard mulCarry' 17 17 = (33, 1)

/-- calculates: a - b - borrowIn.
Logic:
  1. calculate the total subtrahend (b + borrowIn).
  2. ff a >= subtrahend, result is simple subtraction.
  3. if a < subtrahend, we borrow 256 from the next position.
     result becomes (256 + a) - subtrahend.
-/
def subBorrow (a b : FU8 p) (borrow : FB p := 0) : (FU8 p) × (FB p) :=
  -- amount to be subtract
  let subtrahend : ZMod p := b + borrow
  -- check if we need to borrow
  if a.val ≥ subtrahend then (a - subtrahend, 0) -- no borrow
  else ((a + 256) - subtrahend, 1)
  -- borrow (a < b + c), since a < subtrahend, 256 + a - subtrahend < 256

abbrev subBorrow' := @subBorrow prime_babybear

#guard subBorrow' 10 2      = (8, 0)
#guard subBorrow' 10 10     = (0, 0)
#guard subBorrow' 50 0      = (50, 0)
#guard subBorrow' 50 0 1    = (49, 0)
#guard subBorrow' 10 20     = (246, 1)
#guard subBorrow' 10 10 1   = (255, 1)
#guard subBorrow' 255 255   = (0, 0)
#guard subBorrow' 255 255 1 = (255, 1)
#guard subBorrow' 0 255     = (1, 1)
#guard subBorrow' 0 255 1   = (0, 1)
#guard subBorrow' 0 1       = (255, 1)

abbrev Bignum p := List (FU8 p)

namespace Bignum

def normalize (n : Bignum p) : Bignum p :=
  let trimmed := n.rdropWhile (·.val = 0)
  if trimmed.isEmpty then [0] else trimmed

abbrev normalize' := @normalize prime_babybear

#guard normalize' [0] = [0]
#guard normalize' [] = [0]
#guard normalize' [1,0,1,0] = [1,0,1]
#guard normalize' [0,0,0] = [0]
#guard normalize' [0,0,1] = [0, 0, 1]

def ofNatLen (x len : ℕ) : Bignum p :=
  let d := x / 256
  let r := x % 256
  if len = 0 then [] else r :: (ofNatLen d (len - 1))

def ofNat (n : ℕ) : Bignum p :=
  if n == 0 then []
  else
    let digit := n % 256
    let rest := n / 256
    digit :: ofNat rest
decreasing_by
  apply Nat.div_lt_self <;> grind

abbrev ofNat' := @ofNat prime_babybear

#guard ofNat' (255 + 1)  = [0,1]
#guard ofNat' (2^16 + 2) = [2,0,1]

instance (n : ℕ) : OfNat (Bignum p) n where
  ofNat := ofNat n

def toNat : Bignum p → ℕ :=
  List.foldr (fun b acc => acc * 256 + b) 0

abbrev toNat' := @toNat prime_babybear

#guard toNat' [0,1]     = (255 + 1)
#guard toNat' [2,0,1]   = (2^16 + 2)
#guard toNat' [2,0,1,0] = (2^16 + 2)

def add (a b : Bignum p) : Bignum p :=
  loop a b 0
where
  loop (xs ys : Bignum p) (c : FB p) : Bignum p :=
    match xs, ys with
    -- case 1: both lists finished.
    -- if there is a remaining carry, append a new limb [1].
    | [], [] => if c.val == 1 then [1] else []

    -- case 2: 'a' is longer than 'b'.
    -- continue adding carry to 'a' (effectively adding 0 from b).
    -- | x :: xs, [] => let (sum, newC) := fullAdd x 0 c; sum :: loop xs [] newC
    | x :: xs, [] =>
      if c = 0 then x :: xs -- stop recursion if no carry
      else let (sum, newC) := addCarry x 0 c; sum :: loop xs [] newC

    -- Case 3: 'b' is longer than 'a'.
    | [], y :: ys => let (sum, newC) := addCarry 0 y c; sum :: loop [] ys newC

    -- Case 4: Standard addition of two limbs.
    | x :: xs, y :: ys => let (sum, newC) := addCarry x y c; sum :: loop xs ys newC

abbrev add' := @add prime_babybear

#guard (40 : Bignum prime_babybear).add 2 = 42
#guard add' 0 0 = 0
#guard add' 12345 0 = 12345
#guard add' 0 67890 = 67890
#guard add' 10 20 = 30
#guard add'  250   10  =  260
#guard add' [250] [10] = [4,1]
#guard add'  255   1  =  256
#guard add' [255] [1] = [0,1]
#guard add'   65535     1  =   65536
#guard add' [255, 255] [1] = [0, 0, 1]
#guard add' 100000 5 = 100005
#guard add' 200000 10 = 200010
#guard add'  255   255  =    510
#guard add' [255] [255] = [254, 1]
#guard add' 43690 21845 = 65535

def mulOneLine (xs : Bignum p) (s : FU8 p) : Bignum p :=
  loop xs 0
where
  loop i carry :=
    match i with
    | [] => if carry.val > 0 then [carry] else []
    | x :: xs => let (nl, nc) := mulCarry x s carry; nl :: loop xs nc

abbrev mulOneLine' := @mulOneLine prime_babybear

-- TODO: how to deal with multiple zero representation
#guard mulOneLine' 0 0 = 0
#guard mulOneLine' 65535 0 = [0, 0]
#guard mulOneLine' 0 255 = []
#guard mulOneLine' 65535 1 = 65535
#guard mulOneLine' 1 253 = 253
#guard mulOneLine' 65535 2 = ofNat' (65535 * 2)
#guard mulOneLine' 1000 250 = ofNat' (1000 * 250)
#guard mulOneLine' 65535 255 = ofNat' (65535 * 255)
#guard mulOneLine' 10 10 = 100
#guard mulOneLine' 222 2 = 444
#guard mulOneLine' 255 255 = 65025
#guard mulOneLine' 65537 3 = 196611

def mul (a b : Bignum p) : Bignum p :=
  match b with
  | [] => []
  | b :: bs =>
    let rest := mul a bs
    (mulOneLine a b).add (if rest.isEmpty then [] else 0 :: rest)

abbrev mul' := @mul prime_babybear

#guard mul' 0 65535 = []
#guard mul' 65535 0 = []
#guard mul' 1 123456789 = 123456789
#guard mul' 123456789 1 = 123456789
#guard mul' 10 10 = 100
#guard mul' 255 255 = 65025
#guard mul' 256 256 = 65536
#guard mul' 2 100000 = 200000
#guard mul' 100000 2 = 200000
#guard mul' 65535 65535 = 4294836225
#guard mul' 12345 67890 = 838102050

-- RSA-100 factorization
#eval mul' 37975227936943673922808872755445627854565536638199
           40094690950920881030683735292761468389214899724061 =
           1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139

-- RSA-250
#eval mul' 64135289477071580278790190170577389084825014742943447208116859632024532344630238623598752668347708737661925585694639798853367
           33372027594978156556226010605355114227940760344767554666784520987023841729210037080257448673296881877565718986258036932062711
           =
           2140324650240744961264423072839333563008614715144755017797754920881418023447140136643345519095804679610992851872470914587687396261921557363047454770520805119056493106687691590019759405693457452230589325976697471681738069364894699871578494975937497937

/--
  subtracts two bignums (a - b).
  assumes a >= b
  If a < b, this performs modular subtraction (wrapping around) supposedly XD.
-/
def sub (a b : Bignum p) : Bignum p :=
  normalize (loop a b 0)
where
  loop xs ys (borrow : FB p) :=
    match xs, ys with
    -- If borrow is 1 here, it means a < b (underflow). We ignore it for Nat subtraction.
    | [], [] => []
    -- We subtract 0 (and the borrow) from 'a'.
    | x :: xs, [] =>
      let (diff, newBorrow) := subBorrow x 0 borrow
      diff :: loop xs [] newBorrow
    -- subtract 0 (and the borrow) from 'b'.
    | [], y :: ys =>
      let (diff, newBorrow) := subBorrow y 0 borrow
      diff :: loop [] ys newBorrow
    -- standard subtraction
    | x :: xs, y :: ys =>
      let (diff, newBorrow) := subBorrow x y borrow
      diff :: loop xs ys newBorrow

abbrev sub' := @sub prime_babybear

#guard sub' 123456 0 = 123456
#guard sub' 987654 987654 = [0]
#guard sub' 20 10 = 10
#guard sub' 256 1 = 255
#guard sub' 65536 1 = 65535
#guard sub' 1000 10 = 990
#guard sub' 65535 255 = 65280
#guard sub' 100000 99999 = 1
#guard sub' 256 255 = 1
#guard sub' 12345678  8765432 = 3580246

-- returns a <= b (assuming LSB)
def le (a b : Bignum p) : Bool :=
  let an := a.normalize
  let bn := b.normalize
  if an.length < bn.length then true
  else if an.length > bn.length then false
  else -- equal lengths, compare msb to lsb
    compareLists an.reverse bn.reverse
where
  compareLists : Bignum p → Bignum p → Bool
    | [], [] => true
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys =>
      if x.val < y.val then true
      else if x.val > y.val then false
      else compareLists xs ys

abbrev le' := @le prime_babybear

#guard (toNat' [0, 0, 1] ≤ toNat' [0, 10, 0]) = le' [0, 0, 1] [0, 10, 0]

-- Long Division algorithm
-- we cannot easily estimate the quotient digit without some sort of division, but we can "brute force" it.
-- "digit" range is small (0 ... 255), we can find the correct quotient byte by guessing:
-- we try values and multiply to see if it fits

-- TODO: binary search
-- find the largest q ∈ (0..255) such that (divisor * q) <= current_rem using linear search
-- Returns (q, current_rem - divisor * q)
def findQuotientByte (current_rem divisor : Bignum p) : FU8 p × Bignum p :=
  -- tries q from 255 down to 0
  go 255
where
  go : ℕ → FU8 p × Bignum p
    | 0 => (0, current_rem) -- If we reached 0, the quotient is 0
    | q_nat@(n + 1) =>
      let q : FU8 p := q_nat
      let product := mulOneLine divisor q
      if le product current_rem then (q, sub current_rem product)
      else go n

abbrev findQuotientByte' := @findQuotientByte prime_babybear

#guard findQuotientByte' [50] [5] = (10, [0])
#guard findQuotientByte' [52] [5] = (10, [2])
#guard findQuotientByte' [5] [10] = (0, [5])
#guard findQuotientByte' [100] [100] = (1, [0])
#guard findQuotientByte' [255] [1] = (255, [0])
#guard findQuotientByte' [10,1] [1,1] = (1, [9]) -- 266 / 257
#guard findQuotientByte'  266    257  = (1, 9)
#guard findQuotientByte' [246, 9] [10] = (255, [0]) -- 2550 / 10 = 255
#guard findQuotientByte' [29] [10] = (2, [9])
#guard findQuotientByte' [0] [50] = (0, [0]) -- 0 / 50 = 0
#guard findQuotientByte' [88, 2] [44, 1] = (2, [0]) -- 600 / 300
#guard findQuotientByte' [100, 0, 255] [0, 0, 1] = (255, [100]) -- 16711780 / 65536
#guard 16711780 / 65536 = 255
#guard 16711780 % 65536 = 100
#guard findQuotientByte' [0, 0, 64, 192] [0, 0, 0, 128] = (1, 1077936128) -- 3225419776 / 2147483648
#guard 3225419776 / 2147483648 = 1
#guard 3225419776 % 2147483648 = 1077936128
#guard findQuotientByte' [8, 0, 0, 4] [255, 255, 255, 1] = (2, [10]) -- 67108872 / 33554431
#guard 67108872 / 33554431 = 2
#guard 67108872 % 33554431 = 10
#guard findQuotientByte' [139, 140, 25, 6] [98, 26, 197, 3] = (1, [41, 114, 84, 2]) -- 63245986 / 102334155

def div (dividend divisor : Bignum p) : Bignum p × Bignum p :=
  let divisor := divisor.normalize -- safe guard
  let dividend := dividend.normalize -- safe guard
  if divisor = [0] then ([0], dividend) -- division by zero, match lean behaviour
  else
    -- process from MSB first
    let (quot_rev, final_rem) : (Bignum p × Bignum p) :=
      dividend.foldr (fun limb (q_acc, rem) =>
      -- shift remainder left by 8 bits (multiply by 256) and add new limb
      -- in LSB rem * 256 = 0 :: rem
      let rem_new := add (0 :: rem) [limb]
      -- find how many times 'divisor' fits into 'rem_new'
      let (q_byte, rem_next) := findQuotientByte rem_new divisor
      (q_byte :: q_acc, rem_next)
    ) ([], [])
    (quot_rev.normalize, final_rem.normalize)

abbrev div' := @div prime_babybear

abbrev ofNat'' a := let a' := ofNat' a; if a'.isEmpty then [0] else a'
abbrev res a b := (ofNat'' a, ofNat'' b)

#guard let a := 72;      let b := 8;      div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 300;     let b := 5;      div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 50;      let b := 100;    div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 1971210; let b := 1;      div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 512;     let b := 2;      div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 123456;  let b := 0;      div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 1000;    let b := 300;    div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 65535;   let b := 32767;  div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 256;     let b := 10;     div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 729399;  let b := 729399; div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 43690;   let b := 85;     div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 18446744073709551615
       let b := 255
       div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 3901248046479193657
       let b := 123456789
       div' (ofNat a) (ofNat b) = res (a / b) (a % b)
#guard let a := 102337675
       let b := 63248994
       div' (ofNat a) (ofNat b) = res (a / b) (a % b)

-- big boys test
-- RSA-100
#guard let a := 1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139
       let b := 37975227936943673922808872755445627854565536638199
       div' (ofNat a) (ofNat b) = res 40094690950920881030683735292761468389214899724061 0
#guard let a := 1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139
       let b := 40094690950920881030683735292761468389214899724061
       div' (ofNat a) (ofNat b) = res 37975227936943673922808872755445627854565536638199 0

-- RSA-250
#guard let a := 2140324650240744961264423072839333563008614715144755017797754920881418023447140136643345519095804679610992851872470914587687396261921557363047454770520805119056493106687691590019759405693457452230589325976697471681738069364894699871578494975937497937
       let b := 64135289477071580278790190170577389084825014742943447208116859632024532344630238623598752668347708737661925585694639798853367
       div' (ofNat a) (ofNat b) = res 33372027594978156556226010605355114227940760344767554666784520987023841729210037080257448673296881877565718986258036932062711 0
#guard let a := 2140324650240744961264423072839333563008614715144755017797754920881418023447140136643345519095804679610992851872470914587687396261921557363047454770520805119056493106687691590019759405693457452230589325976697471681738069364894699871578494975937497937
       let b := 33372027594978156556226010605355114227940760344767554666784520987023841729210037080257448673296881877565718986258036932062711
       div' (ofNat a) (ofNat b) = res 64135289477071580278790190170577389084825014742943447208116859632024532344630238623598752668347708737661925585694639798853367 0

def mulMod (a b m : Bignum p) : Bignum p :=
  (mul a b).div m |>.2

abbrev mulMod' := @mulMod prime_babybear

#guard toNat' (mulMod' 1234 4567 4321) = (1234 * 4567) % 4321
#guard toNat' (mulMod' 18446744073709551615 729399 65535) = (18446744073709551615 * 729399) % 65535
#guard toNat' (mulMod' 43690 729399 65535) = (43690 * 729399) % 65535
#guard toNat' (mulMod' 1971210 1971210 1971210) = (1971210 * 1971210) % 1971210
#guard toNat' (mulMod' 1971210 729399 123456) = (1971210 * 729399) % 123456
#guard toNat' (mulMod' 123456 1971210 729399) = (123456 * 1971210) % 729399

def pow65537Mod (b m : Bignum p) : Bignum p :=
  let d01 := mulMod b b m
  let d02 := mulMod d01 d01 m
  let d03 := mulMod d02 d02 m
  let d04 := mulMod d03 d03 m
  let d05 := mulMod d04 d04 m
  let d06 := mulMod d05 d05 m
  let d07 := mulMod d06 d06 m
  let d08 := mulMod d07 d07 m
  let d09 := mulMod d08 d08 m
  let d10 := mulMod d09 d09 m
  let d11 := mulMod d10 d10 m
  let d12 := mulMod d11 d11 m
  let d13 := mulMod d12 d12 m
  let d14 := mulMod d13 d13 m
  let d15 := mulMod d14 d14 m
  let d16 := mulMod d15 d15 m
  d16.mulMod b m

abbrev pow65537Mod' := @pow65537Mod prime_babybear

#guard pow65537Mod' 0 17 = [0]
#guard pow65537Mod' 1 19 = 1
#guard pow65537Mod' 12345 1 = [0]
#guard (16^65537) % 17 = 16
#guard pow65537Mod' 16 17 = 16
#guard (5 ^ 65537) % 23 = 14
#guard pow65537Mod' 5 23 = 14
#guard (12 ^ 65537) % 15 = 12
#guard pow65537Mod' 12 15 = 12
#guard (987654321 ^ 65537) % 1000000007 = 352162098
#guard pow65537Mod' 987654321 1000000007 = 352162098
#guard (1000000007 ^ 65537) % 1000000007 = 0
#guard pow65537Mod' 1000000007 1000000007 = [0]
#guard (987654321 ^ 65537) % 2 = 987654321 % 2
#guard pow65537Mod' 987654321 2 = ofNat (987654321 % 2)

end Bignum
