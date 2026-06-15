import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.HashToField
import Clap.Poseidon.Poseidon
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform

open Clap.Lang

namespace F8

variable {p : ℕ}

-- https://en.wikipedia.org/wiki/ASCII#Table_of_codes
def isWhitespace (c : F8 p) : Option (FB p) := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  let gt8 ← F8.greaterThan c 8
  let lt14 ← F8.lessThan c 14
  let isLineBreak : FB p := gt8 &&& lt14
  let isSpace ← F8.eq c 32 -- ASCII 32 is space
  isLineBreak ||| isSpace

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
def isSubstringFS_aux {maxStrLen maxSubstrLen : ℕ} (_h : maxSubstrLen ≤ maxStrLen)
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
  let mut strPolyEval : F bn254 := 0
  for l : i in [0:maxStrLen] do
    strPolyEval := strPolyEval + selector[i] * str.data[i] * powers[i]
  -- Step 5: t(α) = Σⱼ substr[j] · powers[j]
  let mut substrPolyEval : F bn254 := 0
  for l : j in [0:maxSubstrLen] do
    substrPolyEval := substrPolyEval + substr.data[j] * powers[j]!
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
noncomputable def diffPoly (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen)
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

/-! ### Spec bridge lemmas -/

/-- low ↔ mid. The polynomial identity `ŝ = X^si · t`, together with `ŝ ≠ 0`, holds iff the substring genuinely matches.
   Schwartz–Zippel then says that evaluating at a random `α` reflects this identity -/
lemma selectedStrPoly_eq_iff (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ) :
    (selectedStrPoly str substr.len.val si = X ^ si * substrPoly substr ∧ selectedStrPoly str substr.len.val si ≠ 0)
      ↔ SubstringAt str substr si := by
  sorry

/-- mid ↔ high: under validity, the field predicate matches the decoded-string predicate -/
lemma substringAt_eq_string (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hstr : valid str) (hsub : valid substr) :
    SubstringAt str substr si ↔ SubstringAtString (toString str) (toString substr) si := by
  sorry

/-! ### `isSubstringFS_aux` spec proofs -/

/-- Low spec proof: `isSubstringFS_aux` computes `FB.ofBool` of the polynomial-evaluation check. Composes the
    `arraySelector`, `selectArrayValue`, `F.eq` and `FB.and` equivalences and recognises the running sums as `Polynomial.eval`. -/
lemma isSubstringFS_aux_equiv (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (substr : FString bn254 maxSubstrLen)
    (startIndex α : ZMod bn254)
    (hstr : valid str) (hsub : valid substr)
    (hidx : startIndex.val + substr.len.val ≤ maxStrLen)
    (hsi : startIndex.val < maxStrLen) :
    FString.isSubstringFS_aux h str substr startIndex (powersVec α maxStrLen)
      = some (FB.ofBool (isSubstringFS_aux_spec str substr startIndex.val α)) := by
  sorry

/-- (Completness) If the substring matches then, for every challenge that is not a root of `ŝ`, the check passes. The equality half holds
    for *all* `α` (formal identity); only the `ŝ(α) ≠ 0` guard can fail, on at most `deg ŝ < maxStrLen` challenges. -/
lemma isSubstringFS_aux_complete (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hmatch : SubstringAt str substr si)
    (α : ZMod bn254) (hα : (selectedStrPoly str substr.len.val si).eval α ≠ 0) :
    isSubstringFS_aux_spec str substr si α = true := by
  sorry

/-- (Soundness deterministic) If the substring does not match, then `diffPoly` is a non-zero polynomial of degree `< maxStrLen`,
    so the check accepts for at most `maxStrLen - 1` challenges (its roots `Polynomial.card_roots'`) -/
lemma isSubstringFS_aux_sound_card (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hbad : ¬ SubstringAt str substr si) :
    -- the set of all challenges α for which the check passes
    (Finset.univ.filter (fun α => isSubstringFS_aux_spec str substr si α = true)).card ≤ maxStrLen - 1 := by
  sorry

/-- (soundness probabilistic) For a uniformly random challenge `α` (the random-oracle / Fiat–Shamir heuristic on Poseidon), a non-matching
    substring is accepted with probability at most `(maxStrLen - 1) / |F|` (`MvPolynomial.schwartz_zippel`). -/
lemma isSubstringFS_aux_sound_prob (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (si : ℕ)
    (hbad : ¬ SubstringAt str substr si) :
    -- if the substring doesn't match, then when α is drawn uniformly at random, the probability the check passes is at most (maxStrLen − 1) / |F|
    -- outermeasure should be fine since ZMod bn254 is finite
    (PMF.uniformOfFintype (ZMod bn254)).toOuterMeasure {α | isSubstringFS_aux_spec str substr si α = true}
      ≤ ((maxStrLen - 1 : ℕ) : ENNReal) / (Fintype.card (ZMod bn254) : ENNReal) := by
  sorry

/-! ### `isSubstringFS` the full circuit, with the challenge -/

/-- `isSubstringFS` reduces to the low check at the Fiat–Shamir challenge it derives. Composes `powers`-correctness with
    `isSubstringFS_aux_equiv`. -/
lemma isSubstringFS_equiv (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (startIndex : ZMod bn254)
    (hstr : valid str) (hsub : valid substr)
    (hidx : startIndex.val + substr.len.val ≤ maxStrLen)
    (hsi : startIndex.val < maxStrLen) :
    FString.isSubstringFS h str strHash substr startIndex
      = (challenge strHash substr startIndex).map (fun α => FB.ofBool (isSubstringFS_aux_spec str substr startIndex.val α)) := by
  sorry

/-- (probabilistic soundness of the full circuit) Modelling the derived challenge as uniform (the Fiat–Shamir heuristic on Poseidon), the full
    circuit accepts a string/index that is not a genuine substring occurrence with probability at most `(maxStrLen - 1) / |F|` -/
lemma isSubstringFS_sound (str : FString bn254 maxStrLen)
    (substr : FString bn254 maxSubstrLen) (startIndex : ZMod bn254)
    (hstr : valid str) (hsub : valid substr)
    (hbad : ¬ SubstringAtString (toString str) (toString substr) startIndex.val) :
    (PMF.uniformOfFintype (ZMod bn254)).toOuterMeasure {α | isSubstringFS_aux_spec str substr startIndex.val α = true}
      ≤ ((maxStrLen - 1 : ℕ) : ENNReal) / (Fintype.card (ZMod bn254) : ENNReal) := by
  sorry

/-- (completeness of the full circuit) A genuine substring occurrence is accepted whenever the derived challenge avoids the (≤ `maxStrLen-1`) roots of `ŝ`. -/
lemma isSubstringFS_complete (h : maxSubstrLen ≤ maxStrLen)
    (str : FString bn254 maxStrLen) (strHash : ZMod bn254)
    (substr : FString bn254 maxSubstrLen) (startIndex α : ZMod bn254)
    (hstr : valid str) (hsub : valid substr)
    (hmatch : SubstringAtString (toString str) (toString substr) startIndex.val)
    (hchal : challenge strHash substr startIndex = some α)
    (hα : (selectedStrPoly str substr.len.val startIndex.val).eval α ≠ 0) :
    FString.isSubstringFS h str strHash substr startIndex = some FB.true := by
  sorry

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
