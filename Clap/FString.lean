import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.HashToField
import Clap.Poseidon.Poseidon
import Clap.RandomOracle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform

open Clap.Lang

namespace F8

variable {p : ℕ}

def Constraint := Prop

abbrev CircuitOptionM (output       : Type) : Type := Option output
abbrev CircuitContM   (input output : Type) : Type := ExceptT String (Cont (r := input)) output
abbrev CircuitStateM  (output       : Type) : Type := ExceptT String (StateM (List Constraint)) output

-- https://en.wikipedia.org/wiki/ASCII#Table_of_codes
def isWhitespace (c : F8 p) : CircuitOptionM (FB p) := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  let gt8 ← F8.greaterThan c 8
  let lt14 ← F8.lessThan c 14
  let isLineBreak : FB p := gt8 &&& lt14
  let isSpace ← F8.eq c 32 -- ASCII 32 is space
  isLineBreak ||| isSpace

namespace Ops

def num2bitsLsbPureV (n : ℕ) (f : ZMod p) : Vector (ZMod p) n :=
  (aux n f).reverse
where
  aux (n : ℕ) (f : ZMod p) : Vector (ZMod p) n :=
  match n with
  | 0 => #v[]
  | n+1 =>
    let bit := f.val % 2
    let rem := f.val / 2
    (aux n rem).push bit

end Ops

namespace Cont

#synth Pure (Except _)
@[irreducible]
def num2bits (w : ℕ) (e : ZMod p) (input : Type) : CircuitContM input (Vector (ZMod p) w) :=
  if e.val < 2^w
  then ExceptT.lift (pure (Ops.num2bitsLsbPureV w e))
  else ExceptT.

def lessThan (w : ℕ) (a b : F p) (input : Type) : CircuitContM (FB p) input := do
  let d := a - b + 2^w
  let d ← num2bits (w + 1) d
  return FB.not d[w]!

def greaterThan (a b : F8 p) (input : Type) : CircuitContM (FB p) input :=
  lessThan 8 b a

end Cont

def isWhitespaceContM (c : F8 p) (input : Type) : CircuitContM (FB p) input := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  let gt8 ← F8.greaterThan c 8
  let lt14 ← F8.lessThan c 14
  let isLineBreak : FB p := gt8 &&& lt14
  let isSpace ← F8.eq c 32 -- ASCII 32 is space
  isLineBreak ||| isSpace

def isWhitespaceStateM (c : F8 p) : CircuitStateM (FB p) := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  sorry
  -- let gt8 ← F8.greaterThan c 8
  -- let lt14 ← F8.lessThan c 14
  -- let isLineBreak : FB p := gt8 &&& lt14
  -- let isSpace ← F8.eq c 32 -- ASCII 32 is space
  -- isLineBreak ||| isSpace

end F8

namespace Spec.F8

variable {p : ℕ}

def isWhitespace_spec (c:Char) : Bool :=
  (c.toNat > 8 && c.toNat < 14) || c.toNat = 32

lemma toChar_toNat (c : ZMod p) (h : Spec.F8.valid c) : (Spec.F8.toChar c).toNat = c.val := by
  unfold Spec.F8.toChar Spec.F8.toUInt8
  show (UInt8.ofNat c.val).toUInt32.toNat = c.val
  rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

open Clap.Lang.Spec in
lemma isWhitespace_equiv [Fact (Nat.Prime p)] (c:F8 p) (h : Spec.F8.valid c) (h : 2^(8+1) < p) :
  F8.isWhitespace c = some (FB.ofBool (isWhitespace_spec (F8.toChar c))) := by
  unfold F8.isWhitespace isWhitespace_spec F8.greaterThan
  rw [F8.lessThan_equiv] <;> try (first | assumption | aesop (add simp [F8.valid]) ; erw [ZMod.val_natCast_of_lt] <;> grind)
  rw [F8.lessThan_equiv] <;> try (first | assumption | aesop (add simp [F8.valid]) ; erw [ZMod.val_natCast_of_lt] <;> grind)
  simp only [F8.eq,F.eq,F.isZero_def]
  simp [Option.bind_some]
  rw [FB.and_equiv] <;> try apply Spec.FB.valid_ofBool
  rw [FB.or_equiv] <;> try apply Spec.FB.valid_ofBool
  . rw [toChar_toNat] <;> try assumption
    simp only [Spec.FB.left_inv]
    unfold F8.toUInt8
    erw [ZMod.val_natCast_of_lt] <;> try grind
    erw [ZMod.val_natCast_of_lt] <;> try grind
    congr 4
    . aesop (add simp [sub_eq_zero,F8.valid,UInt8.lt_iff_toNat_lt]) <;> grind
    . aesop (add simp [sub_eq_zero,F8.valid,UInt8.lt_iff_toNat_lt]) <;> grind
    . aesop (add simp [FB.toBool,FB.false,sub_eq_zero,F8.valid])
      . apply ZMod.val_cast_of_lt
        grind
      . rw [← ZMod.natCast_zmod_val c, a]; rfl
  . aesop (add simp [Spec.FB.left_inv,Spec.FB.valid_ofBool,FB.valid])

def isWhitespace_high (c:Char) : Bool :=
  c ∈ ['\t',   -- tab
        '\n',   -- line feed
        '\x0B', -- \∨ vertical tab
        '\x0C', -- \f form feed
        '\x0D', -- \r carriage return
        ' ']    -- space

lemma isWhitespace_eq_isWhitespace_high : isWhitespace_spec = isWhitespace_high := by
  funext c
  unfold isWhitespace_spec isWhitespace_high
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have char_to_nat : ∀ (k : Char) (n : ℕ), k.toNat = n → ((c = k) ↔ c.toNat = n) := by
    intros k n hkn
    constructor
    · intro h; rw [h]; exact hkn
    · intro h
      apply Char.ext
      apply UInt32.toNat.inj
      change c.toNat = k.toNat
      rw [h, ← hkn]
  simp only [char_to_nat '\t' 9 (by decide),
             char_to_nat '\n' 10 (by decide),
             char_to_nat '\x0B' 11 (by decide),
             char_to_nat '\x0C' 12 (by decide),
             char_to_nat '\x0D' 13 (by decide),
             char_to_nat ' ' 32 (by decide)]
  simp only [← Bool.decide_and, ← Bool.decide_or]
  apply decide_eq_decide.mpr
  omega

end Spec.F8

namespace FString

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)]

open FB in
/-- Asserts that every value in `inp` is a valid ASCII digit (i.e., in the range [48, 57]). -/
def assertIsAsciiDigits {maxDigits : ℕ} (inp : FString p maxDigits) : Option Unit := do
  let selector ← FArray.arraySelector maxDigits 0 inp.len
  for i in List.finRange maxDigits do
    let c := inp.data[i]
    let gt ← F.greaterThan 8 c 47
    let lt ← F.lessThan 8 c 58
    let isAsciiDigit := FB.and gt lt
    eq0 ((1 - isAsciiDigit) * (selector[i]))

/--
  Given a vector of ASCII digit characters and a length, interprets the digits as a
  base-10 number and returns it as a single field element.

  Requires `1 ≤ len < maxLen` (does not work when `maxLen ≤ 1`). The number represented must fit in the scalar field.
-/
def asciiDigitsToScalar {maxLen : ℕ} (inp : FString p maxLen) : Option (F p) := do
  assert! 0 < maxLen
  assertIsAsciiDigits inp
  -- accumulators[0] = digits[0] - 48
  let acc₀ : F p := inp.data[0]! - 48
  -- Fold over positions i = 1 .. maxLen-1.
  -- State: (s, ieq_sum, acc)
  --   s       : starts at 1, decremented to 0 at position `inp.len`
  --   ieq_sum : running sum of index_eq[i]; must equal 1 at the end
  --   acc     : accumulated digit value, frozen once s = 0
  let (_, ieq_sum, acc) ← (List.finRange maxLen).drop 1 |>.foldlM
    (fun (state : F p × F p × F p) (i : Fin maxLen) ↦ do
      let (s, ieq_sum, acc) := state
      let ieq       : F p ← share (← F.eq inp.len i.1)
      let s'        : F p ← share (← s - ieq)
      let acc_shift : F p ← share (10 * acc + (inp.data[i] - 48))
      let acc'      : F p ← share ((acc_shift - acc) * s' + acc)
      return (s', ieq_sum + ieq, acc'))
    (1, 0, acc₀)
  -- Exactly one index_eq must have been 1, i.e. len ∈ {1, ..., maxLen-1}
  F.assert_eq ieq_sum 1
  return acc

/--
  Checks whether `substr` appears in `str` starting at `startIndex`.
  Uses direct comparison: for each position j in the substring, extracts `str[startIndex + j]` via one-hot array and compares it with `substr[j]`.
  Positions beyond `substr.len` are automatically true. Fails (returns `none`) when `startIndex ≥ maxStrLen` or `substr.len = 0`.
  O(maxSubstrLen × maxStrLen)
-/
def isSubstring {maxStrLen maxSubstrLen : ℕ} (str : FString p maxStrLen) (substr : FString p maxSubstrLen) (startIndex : F p) : Option (FB p) := do
  -- One-hot mask for startIndex; constrains 0 ≤ startIndex < maxStrLen
  let hot ← FArray.singleOneArray maxStrLen startIndex
  -- Selector for active substr positions [0, substr.len); constrains substr.len > 0
  let substrSel ← FArray.arraySelector maxSubstrLen 0 substr.len
  -- For each position j in the substring, extract and compare
  let success ← (List.finRange maxSubstrLen).foldlM (fun (acc : FB p) (j : Fin maxSubstrLen) ↦ do
    -- Extract str[startIndex + j] via one-hot vector:
    -- Σ_k  hot[k] * str.chars[k + j] evaluates to:
    -- (1) 0 * str.chars[X] = 0             except  startIndex + j
    -- (2) 1 * str.chars[X] = str.chars[X]  only at startIndex + j
    -- Σ_k  hot[k] * str.chars[k + j] = str.chars[startIndex + j]
    let extracted : F p ← share $ (List.finRange maxStrLen).foldl (fun sum (k : Fin maxStrLen) ↦
      if h : k.val + j.val < maxStrLen then
        sum + hot[k] * str.data[k.val + j.val]
      else
        sum
    ) 0
    -- Compare extracted value with substr char
    let matched ← F.eq extracted substr.data[j]
    -- position beyond substr.len → automatically true:
    -- If this position is part of the substring, check the match. If it's padding, skip it (always true)
    let gated := FB.or (FB.not substrSel[j]) matched
    return FB.and acc gated
  ) FB.true
  return success

/-- Asserts that `substr` appears in `str` starting at `startIndex`. -/
def assertIsSubstring {maxStrLen maxSubstrLen : ℕ} (str : FString p maxStrLen) (substr : FString p maxSubstrLen) (startIndex : F p) : Option Unit := do
  FB.assert (← isSubstring str substr startIndex)

def powers (α : F p) : (len : ℕ) → Option (Vector (F p) len)
  | 0 => some #v[]
  | n + 1 => do
    let prev ← powers α n
    let pow_n ← if h : n = 0 then pure (1 : F p) else share (prev[n - 1]'(by omega) * α)
    pure (prev.push pow_n)

open Primes HashToField in
/--
  Fiat-Shamir variant of `isSubstring`.
  Specialised to `Primes.bn254` because Poseidon constants are bn254-only.

  `strHash` is the pre-computed hash of `str` (i.e., `hashBytesToFieldWithLen str.chars str.len`).
  This is taken as a parameter to avoid re-hashing when repeatedly calling this template on the
  same string.
-/
def isSubstringFS_aux {maxStrLen maxSubstrLen : ℕ} (h : maxSubstrLen ≤ maxStrLen)
    (str        : FString bn254 maxStrLen)
    (substr     : FString bn254 maxSubstrLen)
    (startIndex : F bn254)
    (powers     : Vector (F bn254) maxStrLen)
    : Option (FB bn254) := do
  -- Step 1: hash substr and derive the random challenge α
  -- let substrHash ← hashBytesToField substr
  -- random_challenge = H(str_hash, substr_hash, substr_len, start_index)
  -- let α ← Clap.Poseidon.poseidonBN254 #v[strHash, substrHash, substr.len, startIndex]
  -- Step 2: build challenge powers α⁰, α¹, …, α^{maxStrLen-1}
  -- powers[0] = 1, powers[i] = α^i
  -- let powers : Vector (F bn254) maxStrLen ← powers α maxStrLen
--    Vector.ofFn (fun i ↦ (List.iterate (fun x ↦ share (x * α)) 1 (i.val + 1)).getLast!)
  -- Step 3: selector bits for [startIndex, startIndex + substr.len)
  let selector ← FArray.arraySelector maxStrLen startIndex (startIndex + substr.len)
  -- Step 4: selected_str[i] = selector[i] * str[i]; ŝ(α) = Σᵢ selected_str[i] · powers[i]
  let strPolyEval : F bn254 := F.dotProduct (selector.zipWith (· * ·) str.data) powers
  -- Step 5: t(α) = Σⱼ substr[j] · powers[j]  (powers truncated to substr's length)
  let substrPolyEval : F bn254 :=
    F.dotProduct substr.data ((powers.take maxSubstrLen).cast (Nat.min_eq_left h))
  -- Step 6: α^startIndex = SelectArrayValue(powers, startIndex)
  let distinguishingValue ← FArray.selectArrayValue powers startIndex
  -- Step 7: success = NOT(isZero(ŝ(α))) AND isEqual(ŝ(α), α^startIndex · t(α))
  let nonZero : FB bn254 := FB.not (←isZero (←share strPolyEval))
  let polyEq  : FB bn254 ← F.eq strPolyEval (distinguishingValue * substrPolyEval)
  return FB.and nonZero polyEq

open Primes HashToField in
def isSubstringFS {maxStrLen maxSubstrLen : ℕ} (h : maxSubstrLen ≤ maxStrLen)
    (str        : FString bn254 maxStrLen)
    (strHash    : F bn254)
    (substr     : FString bn254 maxSubstrLen)
    (startIndex : F bn254)
    : Option (FB bn254) := do
  -- Step 1: hash substr and derive the random challenge α
  let substrHash ← hashBytesToField substr
  -- random_challenge = H(str_hash, substr_hash, substr_len, start_index)
  let α ← Clap.Poseidon.poseidonBN254 #v[strHash, substrHash, substr.len, startIndex]
  -- Step 2: build challenge powers α⁰, α¹, …, α^{maxStrLen-1}
  -- powers[0] = 1, powers[i] = α^i
  let powers : Vector (F bn254) maxStrLen ← powers α maxStrLen
--    Vector.ofFn (fun i ↦ (List.iterate (fun x ↦ share (x * α)) 1 (i.val + 1)).getLast!)
  -- Step 3: selector bits for [startIndex, startIndex + substr.len)
  isSubstringFS_aux h str substr startIndex powers

open Primes in
/-- Asserts that `substr` appears in `str` starting at `startIndex` (Fiat-Shamir variant). -/
def assertIsSubstringFS {maxStrLen maxSubstrLen : ℕ} (h : maxSubstrLen ≤ maxStrLen)
    (str        : FString bn254 maxStrLen)
    (strHash    : F bn254)
    (substr     : FString bn254 maxSubstrLen)
    (startIndex : F bn254)
    : Option Unit := do
  FB.assert (← isSubstringFS h str strHash substr startIndex)

open Primes HashToField in
/--
  Asserts that `fullStr = left ++ right` (concatenation) using the Fiat-Shamir transform.
  Specialised to `Primes.bn254` because Poseidon constants are bn254-only.

  Enforces:
  - `left` is 0-padded after `left.len` characters
  - `fullStr = left || right` where `||` is concatenation

  Mirrors `circuit/templates/helpers/strings/AssertIsConcatenation.circom` from
  the aptos-labs `keyless-zk-proofs` reference: the CIRCOM template only
  checks left-padding and explicitly states "Assumes `right_len` has been
  validated to be correct outside of this subcircuit, i.e. that `right` is
  0-padded after `right_len` values"
-/
def assertIsConcatenation
    {maxFullLen maxLeftLen maxRightLen : ℕ}
    (_hl : maxLeftLen ≤ maxFullLen) (_hr : maxRightLen ≤ maxFullLen)
    (fullStr : FString bn254 maxFullLen)
    (left    : FString bn254 maxLeftLen)
    (right   : FString bn254 maxRightLen)
    : Option Unit := do
  -- Step 1: hash all three strings and derive the random challenge
  let leftHash  ← hashBytesToField left
  let rightHash ← hashBytesToField right
  let fullHash  ← hashBytesToField {fullStr with len := left.len + right.len}
  let α ← Clap.Poseidon.poseidonBN254 #v[leftHash, rightHash, fullHash, left.len]
  -- Step 2: enforce that left is 0-padded after left.len
  -- rightArraySelector(left_len - 1) gives 1s at positions > left_len - 1, i.e. at [left_len, maxLeftLen)
  let leftSelector ← FArray.rightArraySelector maxLeftLen (left.len - 1)
  for l : i in [0:maxLeftLen] do
    eq0 (leftSelector[i] * left.data[i])
  -- NOTE: right-0-padding is deliberately NOT enforced here; per the CIRCOM
  -- reference the caller validates `right_len` (see the doc comment above).
  -- Step 3: build challenge powers α⁰, α¹, …, α^{maxFullLen-1}
  let powers : Vector (F bn254) maxFullLen ← powers α maxFullLen
  -- Step 4: left_poly_eval = Σᵢ left[i] · powers[i]
  let mut leftPolyEval : F bn254 := 0
  for l : i in [0:maxLeftLen] do
    leftPolyEval := leftPolyEval + left.data[i] * powers[i]!
  -- Step 5: right_poly_eval = Σⱼ right[j] · powers[j]
  let mut rightPolyEval : F bn254 := 0
  for l : j in [0:maxRightLen] do
    rightPolyEval := rightPolyEval + right.data[j] * powers[j]!
  -- Step 6: full_poly_eval = Σₖ fullStr[k] · powers[k]
  let mut fullPolyEval : F bn254 := 0
  for l : k in [0:maxFullLen] do
    fullPolyEval := fullPolyEval + fullStr.data[k] * powers[k]
  -- Step 7: distinguishing_value = α^left_len = SelectArrayValue(powers, left_len)
  let distinguishingValue ← FArray.selectArrayValue powers left.len
  -- Step 8: assert full_poly_eval = left_poly_eval + α^left_len · right_poly_eval
  F.assert_eq fullPolyEval (leftPolyEval + distinguishingValue * rightPolyEval)

end FString

/-!
## Spec: `isSubstringFS` (Fiat–Shamir substring check)

`FString.isSubstringFS` / `isSubstringFS_aux` do not compare bytes directly.
They use the Fiat–Shamir + Schwartz–Zippel trick: the selected window of `str`
and the whole `substr` are read as the coefficients of two formal polynomials,
a random challenge `α` is drawn (a Poseidon hash of the inputs), and the polynomial identity `ŝ(X) = X^startIndex · t(X)` is checked at the point `α`.

Here it is specify in three refinement levels:

* Level 1 (low): `isSubstringFS_aux_spec str substr si α` is the polynomial-evaluation
  check at a given `α` (this is what the circuit's `for`-loops actually compute, recognised as `Polynomial.eval`).
* Level 2 (mid): `SubstringAt str substr si` is the field-level substring predicate,
  bridged to Level 1 by `selectedStrPoly_eq_iff` (the formal identity `ŝ = X^si · t` holds iff the substring genuinely matches).
  t(X) = substr[0] + substr[1]·X + substr[2]·X² + … is the substring represented as a polynominal.
  X^si · t(X) we are shifting the string: t(X) describes the substring sitting at position 0 and X^si · t(X) describes that same substring slid over to start at position si,
  which is precisely where it's supposed to live inside str. The substring macthes if these two polynomials ŝ and X^si · t are equal.
* Level 3 (high): `SubstringAtString` is the highlevel lean String/Char meaning, bridged to Level 2 by `substringAt_eq_string` under `Spec.FString.valid`.

Soundness is the Schwartz–Zippel statement, given in two forms:
(1) `..._sound_card` (deterministic: at most `maxStrLen-1` bad challenges, via
`Polynomial.card_roots'`) and (2) `..._sound_prob` (probabilistic: for uniform `α`
the false-accept probability is `≤ (maxStrLen-1)/|F|`). The challenge produced by
Poseidon is !ASSUMED! uniform (the random-oracle / Fiat–Shamir heuristic); this assumption is an explicit hypothesis
-/

namespace Spec.FString

open Primes Polynomial Clap.Lang.Spec.FString

variable {maxStrLen maxSubstrLen : ℕ}

/-- `t(X) = Σⱼ substr[j] · Xʲ` the substring as a formal polynomial. -/
noncomputable def substrPoly (substr : FString bn254 maxSubstrLen) : (ZMod bn254)[X] :=
  ∑ j : Fin maxSubstrLen, C substr.data[j] * X ^ (j : ℕ)

/-- `ŝ(X) = Σ_{i ∈ [si, si+sl)} str[i] · Xⁱ` the selected window of `str` (the coefficients outside the window are
  zeroed by the circuit's `selector`). -/
noncomputable def selectedStrPoly (str : FString bn254 maxStrLen) (sl si : ℕ) : (ZMod bn254)[X] :=
  ∑ i : Fin maxStrLen, if si ≤ (i : ℕ) ∧ (i : ℕ) < si + sl then C str.data[i] * X ^ (i : ℕ) else 0

/-- The difference polynomial -/
noncomputable def isSubstringFS_diffPoly (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen)
    (si : ℕ) : (ZMod bn254)[X] := selectedStrPoly str substr.len.val si - X ^ si * substrPoly substr

/-- (Low) What `isSubstringFS_aux` computes at a given challenge `α`: evaluate `ŝ` and `t` at `α` and check the shifted identity together with the
    non-zero guard `ŝ(α) ≠ 0`. The circuit's running sums are exactly these `Polynomial.eval`s -/
noncomputable def isSubstringFS_aux_spec (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ) (α : ZMod bn254) : Bool :=
  decide ((selectedStrPoly str substr.len.val si).eval α ≠ 0 ∧
          (selectedStrPoly str substr.len.val si).eval α = α ^ si * (substrPoly substr).eval α)

/-- (Mid) Field-level: `substr` matches `str` starting at `si`.
    Bounds + per-byte equality on the window + `substr` zero-padding past its
    length + the window is not all-zero (mirrors the circuit's `ŝ(α) ≠ 0` guard, which rejects a degenerate and out-of-range selector). -/
def SubstringAt (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen) (si : ℕ) : Prop :=
  0 < substr.len.val ∧ si + substr.len.val ≤ maxStrLen ∧
  (∀ j, j < substr.len.val → str.data[si + j]? = substr.data[j]?) ∧
  (∀ j, substr.len.val ≤ j → j < maxSubstrLen → substr.data[j]? = some 0) ∧
  (∃ j, j < substr.len.val ∧ str.data[si + j]? ≠ some 0)

/-- (High) `sub` is non-empty and occurs in `s` starting exactly at character position `si`. -/
def SubstringAtString (s sub : String) (si : ℕ) : Prop :=
  sub ≠ "" ∧ si + sub.length ≤ s.length ∧ sub.toList <+: s.toList.drop si

/-- The power vector `#[α⁰, α¹, …, α^{len-1}]` that `FString.powers` computes -/
def powersVec (α : ZMod bn254) (len : ℕ) : Vector (ZMod bn254) len :=
  Vector.ofFn (fun i => α ^ (i : ℕ))

open HashToField in
/-- The Fiat–Shamir challenge derived by the full `isSubstringFS` circuit. -/
def challenge (strHash : ZMod bn254) (substr : FString bn254 maxSubstrLen) (startIndex : ZMod bn254) : Option (ZMod bn254) := do
  let substrHash ← hashBytesToField substr
  Clap.Poseidon.poseidonBN254 #v[strHash, substrHash, substr.len, startIndex]

/-- The 4-element Poseidon input for one `isSubstringFS` call.
    `substrHash` is the pre-computed `hashBytesToField substr`; passed explicitly so the RO
    model can name this specific query in a soundness lemma. -/
def isSubstringFS_Query (strHash substrHash subLen startIndex : ZMod bn254) : List (ZMod bn254) :=
  [strHash, substrHash, subLen, startIndex]

/-- The 4-element Poseidon input for one `assertIsConcatenation` call. -/
def assertIsConcatenation_Query (leftHash rightHash fullHash leftLen : ZMod bn254) : List (ZMod bn254) :=
  [leftHash, rightHash, fullHash, leftLen]

/-! ### Spec bridge lemmas -/

/-- `coeff` of `substrPoly` at degree `m` is the `m`-th byte of `substr` (zero past the buffer). -/
lemma substrPoly_coeff (substr : FString bn254 maxSubstrLen) (m : ℕ) :
    (substrPoly substr).coeff m = (substr.data[m]?).getD 0 := by
  unfold substrPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < maxSubstrLen
  · rw [Finset.sum_eq_single_of_mem (⟨m, hm⟩ : Fin maxSubstrLen) (Finset.mem_univ _)]
    · simp [Vector.getElem?_eq_getElem hm, Fin.getElem_fin]
    · intro b _ hb
      have hbm : m ≠ (b : ℕ) := by intro h; exact hb (Fin.ext h.symm)
      simp [hbm]
  · have hsum : (∑ j : Fin maxSubstrLen, if m = (j : ℕ) then substr.data[j] else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hbm : m ≠ (b : ℕ) := by have := b.isLt; omega
      simp [hbm]
    rw [hsum, Vector.getElem?_eq_none (by omega)]
    rfl

/-- `coeff` of `selectedStrPoly` at degree `n`: the `n`-th byte of `str` inside the window `[si, si+sl)`, else 0. -/
lemma selectedStrPoly_coeff (str : FString bn254 maxStrLen) (sl si n : ℕ) :
    (selectedStrPoly str sl si).coeff n
      = if si ≤ n ∧ n < si + sl then (str.data[n]?).getD 0 else 0 := by
  unfold selectedStrPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [apply_ite (fun p => Polynomial.coeff p n), Polynomial.coeff_C_mul_X_pow,
             Polynomial.coeff_zero]
  by_cases hn : n < maxStrLen
  · rw [Finset.sum_eq_single_of_mem (⟨n, hn⟩ : Fin maxStrLen) (Finset.mem_univ _)]
    · rw [Vector.getElem?_eq_getElem hn]
      simp [Fin.getElem_fin]
    · intro b _ hb
      have hbn : n ≠ (b : ℕ) := by intro h; exact hb (Fin.ext h.symm)
      simp [hbn]
  · have hsum : (∑ i : Fin maxStrLen,
        if si ≤ (i : ℕ) ∧ (i : ℕ) < si + sl then (if n = (i : ℕ) then str.data[i] else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hbn : n ≠ (b : ℕ) := by have := b.isLt; omega
      simp [hbn]
    rw [hsum, Vector.getElem?_eq_none (by omega)]
    simp

/-- low ↔ mid. The polynomial identity `ŝ = X^si · t`, together with `ŝ ≠ 0`, holds iff the substring genuinely matches.
   Schwartz–Zippel then says that evaluating at a random `α` reflects this identity. -/
lemma selectedStrPoly_eq_iff (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hsub : valid substr)
    (hidx : si + substr.len.val ≤ maxStrLen) :
    (selectedStrPoly str substr.len.val si = X ^ si * substrPoly substr ∧
      selectedStrPoly str substr.len.val si ≠ 0)
      ↔ SubstringAt str substr si := by
  obtain ⟨_, hlt, hpad⟩ := hsub
  -- coeff of the shifted substr poly `X^si · t`
  have hTc : ∀ n, (X ^ si * substrPoly substr).coeff n
      = if si ≤ n then (substr.data[n - si]?).getD 0 else 0 := by
    intro n
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h : si ≤ n
    · rw [if_pos h, if_pos h, substrPoly_coeff]
    · rw [if_neg h, if_neg h]
  constructor
  · -- forward: identity ∧ nonzero → SubstringAt
    rintro ⟨hid, hnz⟩
    rw [Polynomial.ext_iff] at hid
    simp only [selectedStrPoly_coeff, hTc] at hid
    rw [ne_eq, Polynomial.ext_iff, not_forall] at hnz
    simp only [Polynomial.coeff_zero, selectedStrPoly_coeff] at hnz
    obtain ⟨n0, hn0⟩ := hnz
    have hcond0 : si ≤ n0 ∧ n0 < si + substr.len.val := by
      by_contra hc
      rw [if_neg hc] at hn0
      exact hn0 rfl
    rw [if_pos hcond0] at hn0
    refine ⟨by omega, hidx, ?_, ?_, ?_⟩
    · -- matching on the window
      intro j hj
      have key := hid (si + j)
      rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega : si ≤ si + j),
          Nat.add_sub_cancel_left] at key
      rw [Vector.getElem?_eq_getElem (show si + j < maxStrLen by omega),
          Vector.getElem?_eq_getElem (show j < maxSubstrLen by omega)] at key ⊢
      simpa using key
    · -- substr zero-padding past its length (free from `valid substr`)
      intro j hj1 hj2
      have hz : substr.data[j] = 0 := by
        have := hpad ⟨j, hj2⟩ (by simpa using hj1)
        simpa [Fin.getElem_fin] using this
      rw [Vector.getElem?_eq_getElem hj2, hz]
    · -- the window is not all-zero
      refine ⟨n0 - si, by omega, ?_⟩
      rw [show si + (n0 - si) = n0 by omega]
      intro hcontra
      rw [hcontra] at hn0
      simp at hn0
  · -- backward: SubstringAt → identity ∧ nonzero
    rintro ⟨hslpos, hsiidx, hmatch, hpad', hwit⟩
    refine ⟨?_, ?_⟩
    · -- the formal identity, coefficient by coefficient
      rw [Polynomial.ext_iff]
      intro n
      rw [selectedStrPoly_coeff, hTc]
      by_cases h1 : si ≤ n
      · by_cases h2 : n < si + substr.len.val
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          have hm := hmatch (n - si) (by omega)
          rw [show si + (n - si) = n from by omega] at hm
          rw [hm]
        · rw [if_neg (by omega), if_pos h1]
          by_cases h3 : n - si < maxSubstrLen
          · rw [hpad' (n - si) (by omega) h3]; rfl
          · rw [Vector.getElem?_eq_none (by omega)]; rfl
      · rw [if_neg (by omega), if_neg h1]
    · -- `ŝ ≠ 0` from the non-all-zero witness
      rw [ne_eq, Polynomial.ext_iff, not_forall]
      simp only [Polynomial.coeff_zero, selectedStrPoly_coeff]
      obtain ⟨j, hjsl, hjwit⟩ := hwit
      refine ⟨si + j, ?_⟩
      rw [if_pos ⟨by omega, by omega⟩,
          Vector.getElem?_eq_getElem (show si + j < maxStrLen by omega)]
      rw [Vector.getElem?_eq_getElem (show si + j < maxStrLen by omega)] at hjwit
      simpa using hjwit

/-- `toString` as the decoded char-list of the first `len` bytes. -/
lemma toString_toList {p w} (fs : FString p w) :
    (Spec.FString.toString fs).toList = (fs.data.toList.take fs.len.val).map Spec.F8.toChar := by
  simp only [Spec.FString.toString, String.toList_ofList, Vector.toList_toArray, Vector.toList_take]

/-- Length of the decoded string equals the logical length. -/
lemma toString_length {p w} (fs : FString p w) (h : fs.len.val < w) :
    (Spec.FString.toString fs).length = fs.len.val := by
  rw [← String.length_toList, toString_toList, List.length_map, List.length_take,
      Vector.length_toList]
  omega

/-- Indexed character of the decoded string. -/
lemma toString_getElem? {p w} (fs : FString p w) (i : ℕ) :
    (Spec.FString.toString fs).toList[i]?
      = ((fs.data.toList.take fs.len.val)[i]?).map Spec.F8.toChar := by
  rw [toString_toList, List.getElem?_map]

/-- mid ↔ high: the field predicate matches the decoded-`String` predicate. Needs `nonEmpty substr`
    (no embedded null bytes): otherwise the field-level match can read into `str`'s padding via a
    trailing-null substr, or accept an all-null window that the circuit's `ŝ≠0` guard rejects. -/
lemma substringAt_eq_string (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hstr : valid str) (hsub : nonEmpty substr) :
    SubstringAt str substr si
      ↔ SubstringAtString (Spec.FString.toString str) (Spec.FString.toString substr) si := by
  obtain ⟨hstrb, hstrlt, hstrpad⟩ := hstr
  obtain ⟨⟨hsubb, hsublt, hsubpad⟩, hnz⟩ := hsub
  have hLstr : (Spec.FString.toString str).length = str.len.val := toString_length str hstrlt
  have hLsub : (Spec.FString.toString substr).length = substr.len.val := toString_length substr hsublt
  constructor
  · -- forward: field match → decoded-string match
    rintro ⟨h1, h2, hmatch, _hpad, hwit⟩
    -- the window fits within `str`'s content (else a content byte would meet `str`'s zero padding)
    have hB : si + substr.len.val ≤ str.len.val := by
      by_contra hcon
      rw [not_le] at hcon
      have hjT : str.len.val - si < substr.len.val := by omega
      have hji : str.len.val ≤ si + (str.len.val - si) := by omega
      have hjw : si + (str.len.val - si) < maxStrLen := by omega
      have hz : str.data[si + (str.len.val - si)]? = some 0 := by
        rw [Vector.getElem?_eq_getElem hjw]
        have := hstrpad ⟨si + (str.len.val - si), hjw⟩ (by simpa using hji)
        simpa [Fin.getElem_fin] using this
      have hmj := hmatch (str.len.val - si) hjT
      rw [hz] at hmj
      exact hnz (str.len.val - si) hjT hmj.symm
    refine ⟨?_, ?_, ?_⟩
    · -- nonempty
      intro heq
      rw [heq] at hLsub
      simp at hLsub
      omega
    · -- length bound
      rw [hLstr, hLsub]; exact hB
    · -- prefix
      rw [List.prefix_iff_getElem?]
      intro i hi
      have hiT : i < substr.len.val := by
        have h' := hi; rwa [String.length_toList, hLsub] at h'
      have hc1 : si + i < str.len.val := by omega
      rw [← List.getElem?_eq_getElem hi, List.getElem?_drop,
          toString_getElem? str (si + i), toString_getElem? substr i]
      simp only [List.getElem?_take, Vector.getElem?_toList, hc1, hiT, if_true, hmatch i hiT]
  · -- backward: decoded-string match → field match
    rintro ⟨hne, hle, hpre⟩
    rw [hLstr, hLsub] at hle
    rw [List.prefix_iff_getElem?] at hpre
    have hmatch3 : ∀ j, j < substr.len.val → str.data[si + j]? = substr.data[j]? := by
      intro j hj
      have hjL : j < (Spec.FString.toString substr).toList.length := by
        rw [String.length_toList, hLsub]; exact hj
      have hp := hpre j hjL
      rw [← List.getElem?_eq_getElem hjL, List.getElem?_drop,
          toString_getElem? str (si + j), toString_getElem? substr j] at hp
      have hsijw : si + j < maxStrLen := by omega
      have hjw : j < maxSubstrLen := by omega
      have hc1 : si + j < str.len.val := by omega
      simp only [List.getElem?_take, Vector.getElem?_toList, hc1, hj, if_true] at hp
      rw [Vector.getElem?_eq_getElem hsijw, Vector.getElem?_eq_getElem hjw] at hp ⊢
      simp only [Option.map_some] at hp
      have hva := hstrb ⟨si + j, hsijw⟩
      have hvb := hsubb ⟨j, hjw⟩
      simp only [Fin.getElem_fin, Spec.F8.valid] at hva hvb
      congr 1
      exact Spec.F8.toChar_inj hva hvb (Option.some.inj hp)
    have h1pos : 0 < substr.len.val := by
      rcases Nat.eq_zero_or_pos substr.len.val with h0 | h0
      · exfalso; apply hne
        simp [Spec.FString.toString, h0]
      · exact h0
    refine ⟨h1pos, by omega, hmatch3, ?_, ?_⟩
    · -- substr zero-padding past its length
      intro j hj1 hj2
      rw [Vector.getElem?_eq_getElem hj2]
      have := hsubpad ⟨j, hj2⟩ (by simpa using hj1)
      simpa [Fin.getElem_fin] using this
    · -- the window is not all-zero
      refine ⟨0, h1pos, ?_⟩
      rw [hmatch3 0 h1pos]
      exact hnz 0 h1pos

/-! ### `isSubstringFS_aux` spec proofs -/

/-- Low spec proof: `isSubstringFS_aux` computes `FB.ofBool` of the polynomial-evaluation check. Composes the
    `arraySelector`, `selectArrayValue`, `F.eq` and `FB.and` equivalences and recognises the running sums as `Polynomial.eval`. -/
lemma isSubstringFS_aux_equiv (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen)
    (startIndex α : ZMod bn254)
    (hidx : startIndex.val + substr.len.val ≤ maxStrLen)
    (hslen : 0 < substr.len.val)
    (hmax : maxStrLen < 2 ^ 250) :
    FString.isSubstringFS_aux h str substr startIndex (powersVec α maxStrLen)
      = some (FB.ofBool (isSubstringFS_aux_spec str substr startIndex.val α)) := by
  -- `startIndex` is in range: from `hidx` + `hslen` (was a separate hypothesis)
  have hsi : startIndex.val < maxStrLen := by omega
  -- numeric bounds for arraySelector + no ZMod wraparound
  have hbn : (2 : ℕ) ^ 250 < bn254 := by decide
  have hlenbn : maxStrLen ≤ bn254 := le_of_lt (lt_trans hmax hbn)
  have hwrap : (startIndex + substr.len).val = startIndex.val + substr.len.val :=
    ZMod.val_add_of_lt (by omega)
  have hmb : 2 ^ (Clap.minBits maxStrLen + 1) < bn254 := by
    have h1 : Clap.minBits maxStrLen ≤ 251 := by
      calc Clap.minBits maxStrLen ≤ Clap.minBits (2 ^ 250) := Clap.minBits_mono (le_of_lt hmax)
        _ = 251 := by rw [Clap.minBits_eq_log_succ (by norm_num), Nat.log_pow (by norm_num)]
    calc 2 ^ (Clap.minBits maxStrLen + 1) ≤ 2 ^ 252 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < bn254 := by decide
  -- the two subcircuit equivalences
  have harr := Spec.FArray.arraySelector_equiv maxStrLen startIndex (startIndex + substr.len)
    hlenbn hsi (by rw [hwrap]; omega)
    (by rw [hwrap]; exact lt_of_le_of_lt hidx (Clap.lt_two_pow_minBits maxStrLen)) hmb
  have hsel : FArray.selectArrayValue (powersVec α maxStrLen) startIndex
      = some (α ^ startIndex.val) := by
    rw [Spec.FArray.selectArrayValue_equiv (powersVec α maxStrLen) startIndex hlenbn]
    simp only [Spec.FArray.selectArrayValue_spec, powersVec, Vector.getElem?_eq_getElem hsi,
               Vector.getElem_ofFn]
  -- `FB.ofBool (decide P) = if P then 1 else 0`
  have hob : ∀ (P : Prop) [Decidable P], FB.ofBool (decide P) = (if P then (1 : ZMod bn254) else 0) := by
    intro P _; by_cases hP : P <;> simp [hP, FB.ofBool, FB.true, FB.false]
  -- the boolean core, abstracted over the two evaluations to avoid expansion
  have key : ∀ a b : ZMod bn254,
      FB.and (FB.not (if a = 0 then (1 : ZMod bn254) else 0)) (if a - b = 0 then (1 : ZMod bn254) else 0)
        = FB.ofBool (decide (a ≠ 0 ∧ a = b)) := by
    intro a b
    rw [hob]
    simp only [FB.not, FB.and, sub_eq_zero]
    split_ifs <;> simp_all
  -- `take`+`cast` of the powers vector is just the shorter powers vector
  have hcast : Vector.cast (Nat.min_eq_left h) ((powersVec α maxStrLen).take maxSubstrLen)
      = powersVec α maxSubstrLen := by
    apply Vector.ext
    intro i hi
    have hmin : i < min maxSubstrLen maxStrLen := by omega
    simp only [Vector.getElem_cast, Vector.getElem_take, powersVec, Vector.getElem_ofFn]
  -- recognise the substr dot product as t(α)
  have hT : F.dotProduct substr.data
        (Vector.cast (Nat.min_eq_left h) ((powersVec α maxStrLen).take maxSubstrLen))
      = (substrPoly substr).eval α := by
    rw [hcast]
    unfold substrPoly
    rw [Spec.F.dotProduct_equiv]
    unfold Spec.F.dotProduct_spec
    rw [Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.getElem_fin, powersVec, Vector.getElem_ofFn, eval_mul, eval_C, eval_pow, eval_X]
  -- recognise the str dot product as ŝ(α)
  have hS : F.dotProduct (Vector.zipWith (· * ·) (Vector.map FB.ofBool
        (FArray.arraySelector_spec maxStrLen startIndex.val (startIndex.val + ZMod.val substr.len)))
        str.data) (powersVec α maxStrLen)
      = (selectedStrPoly str substr.len.val startIndex.val).eval α := by
    unfold selectedStrPoly
    rw [Spec.F.dotProduct_equiv]
    unfold Spec.F.dotProduct_spec
    rw [Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.getElem_fin, Vector.getElem_zipWith, Vector.getElem_map,
               FArray.arraySelector_spec, Vector.getElem_ofFn, powersVec, hob,
               apply_ite (Polynomial.eval α), eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    split_ifs <;> ring
  -- reduce the circuit and compose
  unfold FString.isSubstringFS_aux
  rw [harr]
  simp only [bind, Option.bind, pure]
  rw [hsel, hwrap]
  simp only [share, F.eq, F.isZero_def]
  rw [hS, hT]
  congr 1
  unfold isSubstringFS_aux_spec
  exact key _ _

/-- (Completness) If the substring matches then, for every challenge that is not a root of `ŝ`, the check passes. The equality half holds
    for *all* `α` (formal identity); only the `ŝ(α) ≠ 0` guard can fail, on at most `deg ŝ < maxStrLen` challenges. -/
lemma isSubstringFS_aux_complete (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hsub : valid substr)
    (hmatch : SubstringAt str substr si)
    (α : ZMod bn254) (hα : (selectedStrPoly str substr.len.val si).eval α ≠ 0) :
    isSubstringFS_aux_spec str substr si α = true := by
  have hid : selectedStrPoly str substr.len.val si = X ^ si * substrPoly substr :=
    ((selectedStrPoly_eq_iff str substr si hsub hmatch.2.1).mpr hmatch).1
  unfold isSubstringFS_aux_spec
  rw [decide_eq_true_eq]
  exact ⟨hα, by rw [hid, eval_mul, eval_pow, eval_X]⟩

/-- (Soundness deterministic) If the substring does not match, then `isSubstringFS_diffPoly` is a non-zero polynomial of degree `< maxStrLen`,
    so the check accepts for at most `maxStrLen - 1` challenges (its roots `Polynomial.card_roots'`) -/
lemma isSubstringFS_aux_sound_card (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hsub : valid substr)
    (hidx : si + substr.len.val ≤ maxStrLen)
    (hbad : ¬ SubstringAt str substr si) :
    -- the set of all challenges α for which the check passes
    (Finset.univ.filter (fun α => isSubstringFS_aux_spec str substr si α = true)).card ≤ maxStrLen - 1 := by
  by_cases hs0 : selectedStrPoly str substr.len.val si = 0
  · -- ŝ = 0 ⇒ the accepting set is empty (the `ŝ(α) ≠ 0` guard never holds)
    have hempty : (Finset.univ.filter
        (fun α => isSubstringFS_aux_spec str substr si α = true)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro α _
      unfold isSubstringFS_aux_spec
      rw [decide_eq_true_eq, hs0]
      simp
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- ŝ ≠ 0
    have hM : 0 < maxStrLen := by
      rcases Nat.eq_zero_or_pos maxStrLen with h | h
      · exfalso; apply hs0; subst h; unfold selectedStrPoly; simp
      · exact h
    have hidne : selectedStrPoly str substr.len.val si ≠ X ^ si * substrPoly substr := by
      intro heq
      exact hbad ((selectedStrPoly_eq_iff str substr si hsub hidx).mp ⟨heq, hs0⟩)
    have hdiff : isSubstringFS_diffPoly str substr si ≠ 0 := by
      unfold isSubstringFS_diffPoly; rw [sub_ne_zero]; exact hidne
    -- `isSubstringFS_diffPoly` has degree `< maxStrLen`: its coefficients vanish at `≥ maxStrLen`
    have hdeg : (isSubstringFS_diffPoly str substr si).natDegree ≤ maxStrLen - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hNm : maxStrLen ≤ N := by omega
      unfold isSubstringFS_diffPoly
      rw [Polynomial.coeff_sub]
      have hc1 : (selectedStrPoly str substr.len.val si).coeff N = 0 := by
        rw [selectedStrPoly_coeff]
        split_ifs with h
        · rw [Vector.getElem?_eq_none (by omega)]; rfl
        · rfl
      have hc2 : (X ^ si * substrPoly substr).coeff N = 0 := by
        rw [Polynomial.coeff_X_pow_mul']
        split_ifs with h
        · rw [substrPoly_coeff]
          rcases lt_or_ge (N - si) maxSubstrLen with hlt | hge
          · rw [Vector.getElem?_eq_getElem hlt]
            have hz : substr.data[N - si] = 0 := by
              have := hsub.2.2 ⟨N - si, hlt⟩ (by show substr.len.val ≤ N - si; omega)
              simpa [Fin.getElem_fin] using this
            rw [hz]; rfl
          · rw [Vector.getElem?_eq_none hge]; rfl
        · rfl
      rw [hc1, hc2, sub_zero]
    -- every accepting challenge is a root of `isSubstringFS_diffPoly`
    have hsubR : (Finset.univ.filter
        (fun α => isSubstringFS_aux_spec str substr si α = true)).val
          ⊆ (isSubstringFS_diffPoly str substr si).roots := by
      intro α hα
      rw [Finset.mem_val, Finset.mem_filter] at hα
      obtain ⟨_, hspec⟩ := hα
      unfold isSubstringFS_aux_spec at hspec
      rw [decide_eq_true_eq] at hspec
      obtain ⟨_, heval⟩ := hspec
      rw [Polynomial.mem_roots']
      refine ⟨hdiff, ?_⟩
      show (isSubstringFS_diffPoly str substr si).eval α = 0
      unfold isSubstringFS_diffPoly
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          sub_eq_zero]
      exact heval
    calc (Finset.univ.filter (fun α => isSubstringFS_aux_spec str substr si α = true)).card
        ≤ (isSubstringFS_diffPoly str substr si).natDegree :=
          Polynomial.card_le_degree_of_subset_roots hsubR
      _ ≤ maxStrLen - 1 := hdeg

/-- (soundness probabilistic) For a uniformly random challenge `α` (the random-oracle / Fiat–Shamir heuristic on Poseidon), a non-matching
    substring is accepted with probability at most `(maxStrLen - 1) / |F|` (`MvPolynomial.schwartz_zippel`). -/
lemma isSubstringFS_aux_sound_prob (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hsub : valid substr)
    (hidx : si + substr.len.val ≤ maxStrLen)
    (hbad : ¬ SubstringAt str substr si) :
    -- if the substring doesn't match, then when α is drawn uniformly at random, the probability the check passes is at most (maxStrLen − 1) / |F|
    -- outermeasure should be fine since ZMod bn254 is finite; follows from `isSubstringFS_aux_sound_card`
    (PMF.uniformOfFintype (ZMod bn254)).toOuterMeasure {α | isSubstringFS_aux_spec str substr si α = true}
      ≤ ((maxStrLen - 1 : ℕ) : ENNReal) /  (bn254 : ENNReal) := by
  have hcard := isSubstringFS_aux_sound_card str substr si hsub hidx hbad
  have hset_eq : {α : ZMod bn254 | isSubstringFS_aux_spec str substr si α = true} =
      ↑(Finset.univ.filter (fun α => isSubstringFS_aux_spec str substr si α = true)) := by
    ext α; simp
  rw [hset_eq, PMF.toOuterMeasure_uniformOfFintype_apply, ZMod.card]
  apply ENNReal.div_le_div_right
  simp only [Finset.coe_sort_coe, Fintype.card_coe]
  exact_mod_cast hcard

/-! ### `isSubstringFS` the full circuit, with the challenge -/

/-- The circuit downstream of the Fiat–Shamir challenge: the Poseidon output is replaced by a
    freely-chosen `α`. The full `isSubstringFS` is exactly this, bound after the (Poseidon)
    challenge (see `isSubstringFS_factor`). Factoring the challenge out is what lets the
    random-oracle model put a distribution on `α`. -/
def isSubstringFS_atChallenge (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen)
    (startIndex α : ZMod bn254) : Option (FB bn254) :=
  (FString.powers α maxStrLen).bind (FString.isSubstringFS_aux h str substr startIndex)

/-- The full circuit factors as the (Poseidon) challenge bound into the post-challenge circuit.
    So `{α | isSubstringFS_atChallenge … α = some FB.true}` is precisely the set of challenge
    values for which `isSubstringFS` accepts. -/
lemma isSubstringFS_factor (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (startIndex : ZMod bn254) :
    FString.isSubstringFS h str strHash substr startIndex
      = (challenge strHash substr startIndex).bind
          (isSubstringFS_atChallenge h str substr startIndex) := by
  unfold FString.isSubstringFS challenge isSubstringFS_atChallenge
  simp only [bind, Option.bind]
  split <;> simp_all

/-- `FString.powers α len` always succeeds and equals the spec vector `powersVec α len`. -/
private lemma powers_eq (α : ZMod bn254) (len : ℕ) :
    FString.powers α len = some (powersVec α len) := by
  induction len with
  | zero => simp [FString.powers, powersVec]
  | succ n ih =>
    simp only [FString.powers, ih, bind, Option.bind, pure, share]
    split_ifs with hn
    · subst hn
      congr 1
    · congr 1
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_push, powersVec, Vector.getElem_ofFn]
      split_ifs with hi'
      · rfl
      · have heq : i = n := by omega
        rw [heq]
        have hn' : n - 1 + 1 = n := by omega
        conv_rhs => rw [← hn']
        rw [pow_succ]

/-- `isSubstringFS` reduces to the low check at the Fiat–Shamir challenge it derives. Composes `powers`-correctness with
    `isSubstringFS_aux_equiv`. -/
lemma isSubstringFS_equiv (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (startIndex : ZMod bn254)
    --(hstr : valid str) (hsub : valid substr)
    (hidx : startIndex.val + substr.len.val ≤ maxStrLen)
    --(hsi : startIndex.val < maxStrLen)
    (hslen : 0 < substr.len.val)
    (hmax : maxStrLen < 2 ^ 250) :
    FString.isSubstringFS h str strHash substr startIndex
      = (challenge strHash substr startIndex).map (fun α => FB.ofBool (isSubstringFS_aux_spec str substr startIndex.val α)) := by
  rw [isSubstringFS_factor]
  rcases challenge strHash substr startIndex with _ | α
  · simp
  · simp only [Option.bind_some, Option.map_some]
    unfold isSubstringFS_atChallenge
    rw [powers_eq, Option.bind_some]
    exact isSubstringFS_aux_equiv h str substr startIndex α hidx hslen hmax

/-- (RO soundness — `isSubstringFS`) Under the random-oracle model the Poseidon-derived
    challenge has distribution `ro.chal (isSubstringFS_Query …)`, which `ro.uniform` says is uniform.
    A non-matching input is accepted with probability at most `(maxStrLen − 1) / |F|`. -/
lemma isSubstringFS_sound_RO (ro : ROModel bn254)
    (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (substrHash : ZMod bn254) (startIndex : ZMod bn254)
    (hstr : valid str) (hsub : nonEmpty substr)
    --(hHash  : HashToField.hashBytesToField substr = some substrHash)
    (hidx   : startIndex.val + substr.len.val ≤ maxStrLen)
    (hslen  : 0 < substr.len.val) (hmax : maxStrLen < 2 ^ 250)
    (hbad   : ¬ SubstringAtString (toString str) (toString substr) startIndex.val) :
    (ro.chal (isSubstringFS_Query strHash substrHash substr.len startIndex)).toOuterMeasure
        {α | isSubstringFS_atChallenge h str substr startIndex α = some FB.true}
      ≤ ((maxStrLen - 1 : ℕ) : ENNReal) / bn254 := by
  rw [ro.uniform]
  have hset : {α | isSubstringFS_atChallenge h str substr startIndex α = some FB.true} =
      {α | isSubstringFS_aux_spec str substr startIndex.val α = true} := by
    ext α
    simp only [Set.mem_setOf_eq]
    unfold isSubstringFS_atChallenge
    rw [powers_eq, Option.bind_some,
        isSubstringFS_aux_equiv h str substr startIndex α hidx hslen hmax]
    cases isSubstringFS_aux_spec str substr startIndex.val α <;>
      simp [FB.ofBool, FB.true, FB.false, zero_ne_one]
  rw [hset]
  apply isSubstringFS_aux_sound_prob
  · exact hsub.1
  · exact hidx
  · exact mt (substringAt_eq_string str substr startIndex.val hstr hsub).mp hbad

/-- (completeness of the full circuit) A genuine substring occurrence is accepted whenever the derived challenge avoids the (≤ `maxStrLen-1`) roots of `ŝ`. -/
lemma isSubstringFS_complete (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (startIndex α : ZMod bn254)
    (hstr : valid str) (hsub : valid substr)
    (hmax : maxStrLen < 2 ^ 250)
    (hmatch : SubstringAtString (toString str) (toString substr) startIndex.val)
    (hchal : challenge strHash substr startIndex = some α)
    (hα : (selectedStrPoly str substr.len.val startIndex.val).eval α ≠ 0) :
    FString.isSubstringFS h str strHash substr startIndex = some FB.true := by
  obtain ⟨hne, hle, hpre⟩ := hmatch
  obtain ⟨hstrb, hstrlt, hstrpad⟩ := hstr
  obtain ⟨hsubb, hsublt, hsubpad⟩ := hsub
  have hLstr : (toString str).length = str.len.val := toString_length str hstrlt
  have hLsub : (toString substr).length = substr.len.val := toString_length substr hsublt
  have hslen : 0 < substr.len.val := by
    rcases Nat.eq_zero_or_pos substr.len.val with h0 | h0
    · exfalso; apply hne; simp [Spec.FString.toString, h0]
    · exact h0
  have hle_str : startIndex.val + substr.len.val ≤ str.len.val := by
    have := hle; rw [hLstr, hLsub] at this; exact this
  have hidx : startIndex.val + substr.len.val ≤ maxStrLen := by omega
  rw [List.prefix_iff_getElem?] at hpre
  -- byte-level matching: replicate the backward direction of `substringAt_eq_string`
  have hmatch3 : ∀ j, j < substr.len.val → str.data[startIndex.val + j]? = substr.data[j]? := by
    intro j hj
    have hjL : j < (toString substr).toList.length := by
      rw [String.length_toList, hLsub]; exact hj
    have hp := hpre j hjL
    rw [← List.getElem?_eq_getElem hjL, List.getElem?_drop,
        toString_getElem? str (startIndex.val + j), toString_getElem? substr j] at hp
    have hsijw : startIndex.val + j < maxStrLen := by omega
    have hjw : j < maxSubstrLen := by omega
    have hc1 : startIndex.val + j < str.len.val := by omega
    simp only [List.getElem?_take, Vector.getElem?_toList, hc1, hj, if_true] at hp
    rw [Vector.getElem?_eq_getElem hsijw, Vector.getElem?_eq_getElem hjw] at hp ⊢
    simp only [Option.map_some] at hp
    have hva := hstrb ⟨startIndex.val + j, hsijw⟩
    have hvb := hsubb ⟨j, hjw⟩
    simp only [Fin.getElem_fin, Spec.F8.valid] at hva hvb
    congr 1
    exact Spec.F8.toChar_inj hva hvb (Option.some.inj hp)
  have hSA : SubstringAt str substr startIndex.val := by
    refine ⟨hslen, hidx, hmatch3, ?_, ?_⟩
    · -- condition 4: zero-padding of substr past its length
      intro j hj1 hj2
      rw [Vector.getElem?_eq_getElem hj2]
      have := hsubpad ⟨j, hj2⟩ (by simpa using hj1)
      simpa [Fin.getElem_fin] using this
    · -- condition 5: non-zero window witness; by contradiction via hα
      by_contra hcon
      push_neg at hcon
      -- hcon : ∀ j < substr.len.val, str.data[startIndex.val + j]? = some 0
      apply hα
      suffices hzero : selectedStrPoly str substr.len.val startIndex.val = 0 by simp [hzero]
      rw [Polynomial.ext_iff]
      intro n
      rw [Polynomial.coeff_zero, selectedStrPoly_coeff]
      split_ifs with hn
      · obtain ⟨hge, hlt⟩ := hn
        have hj : n - startIndex.val < substr.len.val := by omega
        have heq : startIndex.val + (n - startIndex.val) = n := by omega
        have hbyte := hcon (n - startIndex.val) hj
        rw [heq] at hbyte
        simp [hbyte]
      · rfl
  have hspec : isSubstringFS_aux_spec str substr startIndex.val α = true :=
    isSubstringFS_aux_complete str substr startIndex.val ⟨hsubb, hsublt, hsubpad⟩ hSA α hα
  rw [isSubstringFS_equiv h str strHash substr startIndex hidx hslen hmax, hchal]
  simp [hspec, FB.ofBool, FB.true]

end Spec.FString

namespace TestString

open Clap.Lang Clap.Spec
open F8 FString

abbrev p := Primes.babybear

private def countTrailingZeros {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (F p) := do
  let res : F p × F p ← Vector.foldlM (fun (len,keepCounting) f ↦ do
    let b ← F.eq f 0
    let len := len + (b * keepCounting)
    let keepCounting := FB.and keepCounting b
    return (len, keepCounting)
  ) (0, FB.true) fs.reverse
  res.1

/--
  Takes an arbitrary vector of field elements and returns a MyString.
  Fails if the input contains an element that is not a byte.
-/
def ofFs {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (FString p maxLen) := do
  let zeros ← countTrailingZeros fs
  let len := maxLen - zeros
  some ⟨fs, len⟩

/-
we could not use `deriving DecidableEq` when we defined FString, because there is no DecidableEq over F.
deriving instance DecidableEq for (FString p 5).
Even after we open ZMod we still don't have it
#synth DecidableEq (FString p 2)
So we define it by hand here.
-/
instance {p m :ℕ} [Fact (Primes.fits p 8)] [DecidableEq (F p)] [DecidableEq (F8 p)]: DecidableEq (FString p m) := by
  intros a b
  rcases a
  rcases b
  simp
  infer_instance

example : countTrailingZeros #v[0,0] = some (2: F p) := by native_decide
example : countTrailingZeros #v[1,0] = some (1: F p) := by native_decide
example : countTrailingZeros #v[0,1,0,0] = some (2: F p) := by native_decide
example : countTrailingZeros #v[0,0,1,0] = some (1: F p) := by native_decide

example : (do ofFs #v[]) = some {data := #v[], len:= (0:F p)} := by native_decide
example : (do ofFs #v[(0:F p),1,0,0]) = some { data := #v[0,1,0,0],len := 2 } := by native_decide

-- isWhitespace tests
example : F8.isWhitespace ( 9 : F p) = some FB.true := by native_decide -- TAB
example : F8.isWhitespace (10 : F p) = some FB.true := by native_decide -- LF
example : F8.isWhitespace (11 : F p) = some FB.true := by native_decide -- VT
example : F8.isWhitespace (12 : F p) = some FB.true := by native_decide -- FF
example : F8.isWhitespace (13 : F p) = some FB.true := by native_decide -- CR
example : F8.isWhitespace (32 : F p) = some FB.true := by native_decide -- SPACE
example : F8.isWhitespace (65 : F p) = some FB.false := by native_decide -- 'A'
example : F8.isWhitespace ( 0 : F p) = some FB.false := by native_decide -- NUL

/-- Construct an `FString` from a char vector and a length for use in tests.
    Notably this allows to construct a "wrong" FString that FString.ofFs would not return. -/
private def mkFStr {n : ℕ} (chars : Vector (F p) n) (len : ZMod p) : FString p n :=
  ⟨chars, len⟩

-- assertIsAsciiDigits tests
example : (do FString.assertIsAsciiDigits (mkFStr #v[48, 57, 0]   2)) = some () := by native_decide
example : (do FString.assertIsAsciiDigits (mkFStr #v[48, 49, 50]  3)) = some () := by native_decide
example : (do FString.assertIsAsciiDigits (mkFStr #v[48, 49, 100] 2)) = some () := by native_decide -- non-digit after len OK
example : (do FString.assertIsAsciiDigits (mkFStr #v[47, 48, 0]   2)) = none := by native_decide    -- '/'=47 below '0'
example : (do FString.assertIsAsciiDigits (mkFStr #v[48, 58, 0]   2)) = none := by native_decide    -- ':'=58 above '9'

-- asciiDigitsToScalar tests
-- ASCII digit mapping: '0'=48 '1'=49 '2'=50 '3'=51 '4'=52 '5'=53 '6'=54 '7'=55 '8'=56 '9'=57
example : (do FString.asciiDigitsToScalar (mkFStr #v[55, 0, 0]              1)) = some 7     := by native_decide -- "7"     → 7
example : (do FString.asciiDigitsToScalar (mkFStr #v[49, 50, 0]             2)) = some 12    := by native_decide -- "12"    → 12
example : (do FString.asciiDigitsToScalar (mkFStr #v[49, 50, 51, 0]         3)) = some 123   := by native_decide -- "123"   → 123
example : (do FString.asciiDigitsToScalar (mkFStr #v[49, 50, 51, 52, 53, 0] 5)) = some 12345 := by native_decide -- "12345" → 12345
example : (do FString.asciiDigitsToScalar (mkFStr #v[48, 0, 0]              1)) = some 0     := by native_decide -- "0"     → 0
example : (do FString.asciiDigitsToScalar (mkFStr #v[51, 48, 53, 0]         3)) = some 305   := by native_decide -- "305"   → 305 ('3'=51 '0'=48 '5'=53)
example : (do FString.asciiDigitsToScalar (mkFStr #v[57, 56, 55, 54, 0]     4)) = some 9876  := by native_decide -- "9876"  → 9876 ('9'=57 '8'=56 '7'=55 '6'=54)
example : (do FString.asciiDigitsToScalar (mkFStr #v[52, 50, 100, 100]      2)) = some 42    := by native_decide -- "42"    → 42 (non-digit padding beyond len ignored)
-- do we want this behaviour?
example : (do FString.asciiDigitsToScalar (mkFStr #v[49, 50, 51]     3)) = none := by native_decide -- len = maxLen: no index_eq fires
example : (do FString.asciiDigitsToScalar (mkFStr #v[57, 56, 55, 54] 4)) = none := by native_decide -- len = maxLen: digits valid but out of range
example : (do FString.asciiDigitsToScalar (mkFStr #v[49, 50, 51]     0)) = none := by native_decide -- len = 0: arraySelector rejects
example : (do FString.asciiDigitsToScalar (mkFStr #v[55]             1)) = none := by native_decide -- maxLen = 1: fold empty, ieq_sum stays 0
example : (do FString.asciiDigitsToScalar (mkFStr #v[65, 49, 0]      2)) = none := by native_decide -- "A1": 'A'=65 not a digit, assertIsAsciiDigits fails

-- isSubstring tests
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'a'=97 'b'=98 'c'=99 'x'=120 'y'=121 'z'=122

-- "hel" in "hello" at 0
example : FString.isSubstring
    (mkFStr #v[104, 101, 108, 108, 111] 5)
    (mkFStr #v[104, 101, 108] 3) 0 = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : FString.isSubstring
    (mkFStr #v[104, 101, 108, 108, 111] 5)
    (mkFStr #v[101, 108, 108] 3) 1 = some FB.true := by native_decide

-- "xyz" in "hello" at 0 (no match)
example : FString.isSubstring
  (mkFStr #v[104, 101, 108, 108, 111] 5)
  (mkFStr #v[120, 121, 122] 3) 0 = some FB.false := by native_decide

-- "lo" in "hello" at 3
example : FString.isSubstring
  (mkFStr #v[104, 101, 108, 108, 111] 5)
  (mkFStr #v[108, 111] 2) 3 = some FB.true := by native_decide

-- Substr extends beyond str → false: "lo" in "hello" at 4
example : FString.isSubstring
  (mkFStr #v[104, 101, 108, 108, 111] 5)
  (mkFStr #v[108, 111, 0] 2) 4 = some FB.false := by native_decide

-- "b" in "abc" at 1
example : FString.isSubstring
  (mkFStr #v[97, 98, 99] 3)
  (mkFStr #v[98] 1) 1 = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : FString.assertIsSubstring
  (mkFStr #v[104, 101, 108, 108, 111] 5)
  (mkFStr #v[101, 108, 108] 3) 1 = some () := by native_decide

-- assertIsSubstring failure: "xyz" in "hello" at 0
example : FString.assertIsSubstring
  (mkFStr #v[104, 101, 108, 108, 111] 5)
  (mkFStr #v[120, 121, 122] 3) 0 = none := by native_decide


-- isSubstringFS tests (bn254-only due to Poseidon)
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'a'=97 'b'=98 'c'=99 'x'=120 'y'=121 'z'=122

abbrev q := Primes.bn254

private def mkFStrQ {n : ℕ} (chars : Vector (F q) n) (len : F q) : FString q n :=
  ⟨chars, len⟩

/-- Compute `strHash` for an `FString` via `hashBytesToFieldWithLen`. -/
private def strHashOf {n : ℕ} (s : FString q n) : Option (F q) :=
  HashToField.hashBytesToField s

-- "hel" in "hello" at 0
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[104, 101, 108] 3) 0
  ) = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[101, 108, 108] 3) 1
  ) = some FB.true := by native_decide

-- "xyz" in "hello" at 0 (no match)
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[120, 121, 122] 3) 0
  ) = some FB.false := by native_decide

-- "lo" in "hello" at 3
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[108, 111] 2) 3
  ) = some FB.true := by native_decide

-- Substr extends beyond str → false: "lo" in "hello" at 4
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[108, 111, 0] 2) 4
  ) = some FB.false := by native_decide

-- "b" in "abc" at 1
example : (do
  let str := mkFStrQ #v[97, 98, 99] 3
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ #v[98] 1) 1
  ) = some FB.true := by native_decide

-- assertIsSubstringFS: "ell" in "hello" at 1
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.assertIsSubstringFS (by omega) str h (mkFStrQ #v[101, 108, 108] 3) 1
  ) = some () := by native_decide

-- assertIsSubstringFS failure: "xyz" in "hello" at 0
example : (do
  let str := mkFStrQ #v[104, 101, 108, 108, 111] 5
  let h ← strHashOf str
  FString.assertIsSubstringFS (by omega) str h (mkFStrQ #v[120, 121, 122] 3) 0
  ) = none := by native_decide

-- assertIsConcatenation tests
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'w'=119 'r'=114 'd'=100 'a'=97 'b'=98 'c'=99

-- 1. "hello" = "hel" ++ "lo" (basic concatenation)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[104, 101, 108, 108, 111] 5)
  (mkFStrQ #v[104, 101, 108] 3)
  (mkFStrQ #v[108, 111] 2)
  = some () := by native_decide

-- 2. "hello" = "h" ++ "ello" (split at 1)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[104, 101, 108, 108, 111] 5)
  (mkFStrQ #v[104] 1)
  (mkFStrQ #v[101, 108, 108, 111] 4)
  = some () := by native_decide

-- 3. "abc" = "ab" ++ "c" (different string)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  (mkFStrQ #v[97, 98] 2)
  (mkFStrQ #v[99] 1)
  = some () := by native_decide

-- 4. maxLen > actual len with 0-padding: full="ab\0" (len=2) = "a\0" (len=1) ++ "b\0" (len=1)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 0] 2)
  (mkFStrQ #v[97, 0] 1)
  (mkFStrQ #v[98, 0] 1)
  = some () := by native_decide

-- 5. Wrong concatenation: "abc" ≠ "ab" ++ "b" (right doesn't match)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  (mkFStrQ #v[97, 98] 2)
  (mkFStrQ #v[98] 1)
  = none := by native_decide

-- 6. Wrong concatenation: "abc" ≠ "ac" ++ "c" (left doesn't match)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  (mkFStrQ #v[97, 99] 2)
  (mkFStrQ #v[99] 1)
  = none := by native_decide

-- 7a. Left 0-padding valid: left = [97, 98, 0] with len=2 passes
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  -- len=2, byte at index 2 is 0 → valid padding
  (mkFStrQ #v[97, 98, 0] 2)
  (mkFStrQ #v[99] 1)
  = some () := by native_decide

-- 7b. Left 0-padding violated: left = [97, 98, 99] with len=2 fails
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  -- len=2, byte at index 2 is non-zero → fails
  (mkFStrQ #v[97, 98, 99] 2)
  (mkFStrQ #v[99] 1)
  = none := by native_decide

-- Right-0-padding is no longer enforced in-subcircuit (the caller validates
-- right_len, per the AssertIsConcatenation reference). Both cases below are
-- therefore decided purely by the concatenation polynomial check.

-- 8a. right = [99, 0] (len=1): the trailing 0 matches `full` → concatenates → some
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  (mkFStrQ #v[97, 98] 2)
  (mkFStrQ #v[99, 0] 1)
  = some () := by native_decide

-- 8b. right = [99, 100] (len=1): the trailing 100 has no matching slot in a
--     maxFullLen=3 `full`, so the polynomial identity fails → none (not a padding check)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ #v[97, 98, 99] 3)
  (mkFStrQ #v[97, 98] 2)
  (mkFStrQ #v[99, 100] 1)
  = none := by native_decide

end TestString
