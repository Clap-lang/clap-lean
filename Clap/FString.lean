import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.HashToField
import Clap.Poseidon.Poseidon

open Clap.Lang Core

abbrev FChar (p : ℕ) [Fact (Primes.fits p 8)] [Core p] := F8 p

namespace FChar

variable {p : ℕ} [core : Core p] [fits : Fact (Primes.fits p 8)]

open FB

def isWhitespace (c : FChar p) : Option (FB p) := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  let bv8  : F8 p := [0, 0, 0, 1, 0, 0, 0, 0]
  let bv14 : F8 p := [0, 1, 1, 1, 0, 0, 0, 0]
  let bv32 : F8 p := [0, 0, 0, 0, 0, 1, 0, 0]
  let gt8 ← FBitVec.greaterThan c bv8
  let lt14 ← FBitVec.lessThan c bv14
  let isLineBreak : FB p := and gt8 lt14
  let isSpace ← F8.eq c bv32 -- ASCII 32 is space
  return or isLineBreak isSpace

end FChar

/--
  Zero-padded vector of bytes of length `len`. `len` can at most be `maxLen`.
-/
structure FString (p : ℕ) [Fact (Primes.fits p 8)] [Core p] (maxLen : ℕ) where
  chars : Vector (FChar p) maxLen
  len : F p

namespace FString

variable {p : ℕ} [core : Core p] [fits : Fact (Primes.fits p 8)]

private def countZeros {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (F p) := do
  Vector.foldlM (fun (len : F p) f ↦ do
    let b ← F.eq f (const 0)
    some (len + convert b)
  ) (const 0) fs

/--
  Takes an arbitrary vector of field elements and returns a MyString.
  Fails if the input contains an element that is not a byte.
-/
def ofVec {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (FString (p := p) maxLen) := do
  let zeros ← countZeros fs
  let len := maxLen - zeros
  let chars ← Vector.mapM F8.ofF fs
  some ⟨chars, len⟩

open FB in
/-- Asserts that every value in `inp` is a valid ASCII digit (i.e., in the range [48, 57]). -/
def assertIsAsciiDigits {maxDigits : ℕ} (inp : FString p maxDigits) : Option Unit := do
  let selector ← FArray.arraySelector maxDigits (const 0) inp.len
  let bv47 : F8 p := [1, 1, 1, 1, 0, 1, 0, 0]
  let bv58 : F8 p := [0, 1, 0, 1, 1, 1, 0, 0]
  for i in List.finRange maxDigits do
    let c := inp.chars[i]
    let gt ← FBitVec.greaterThan c bv47
    let lt ← FBitVec.lessThan c bv58
    let isAsciiDigit := FB.and gt lt
    eq0 (convert $ (1 - isAsciiDigit) * (selector[i]))

/--
  Given a vector of ASCII digit characters and a length, interprets the digits as a
  base-10 number and returns it as a single field element.

  Requires `1 ≤ len < maxLen` (does not work when `maxLen ≤ 1`). The number represented must fit in the scalar field.
-/
def asciiDigitsToScalar {maxLen : ℕ} (inp : FString p maxLen) : Option (F p) := do
  assertIsAsciiDigits inp
  if h : 0 < maxLen then
    -- accumulators[0] = digits[0] - 48
    let acc₀ : F p := inp.chars[0].toF - const (48 : ZMod p)
    -- Fold over positions i = 1 .. maxLen-1.
    -- State: (s, ieq_sum, acc)
    --   s       : starts at 1, decremented to 0 at position `inp.len`
    --   ieq_sum : running sum of index_eq[i]; must equal 1 at the end
    --   acc     : accumulated digit value, frozen once s = 0
    let (_, ieq_sum, acc) := (List.finRange maxLen).drop 1 |>.foldl
      (fun (state : F p × F p × F p) (i : Fin maxLen) ↦
        let (s, ieq_sum, acc) := state
        let ieq       : F p := share $ convert (isZero (inp.len - const (i.1 : ZMod p)))
        let s'        : F p := share $ s - ieq
        let acc_shift : F p := share $ const (10 : ZMod p) * acc + (inp.chars[i].toF - const (48 : ZMod p))
        let acc'      : F p := share $ (acc_shift - acc) * s' + acc
        (s', ieq_sum + ieq, acc'))
      (const (1 : ZMod p), const (0 : ZMod p), acc₀)
    -- Exactly one index_eq must have been 1, i.e. len ∈ {1, ..., maxLen-1}
    F.assert_eq ieq_sum (const (1 : ZMod p))
    return acc
  else
    none

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
  let substrSel ← FArray.arraySelector maxSubstrLen (const 0) substr.len
  -- For each position j in the substring, extract and compare
  let success ← (List.finRange maxSubstrLen).foldlM (fun (acc : FB p) (j : Fin maxSubstrLen) ↦ do
    -- Extract str[startIndex + j] via one-hot vector:
    -- Σ_k  hot[k] * str.chars[k + j] evaluates to:
    -- (1) 0 * str.chars[X] = 0             except  startIndex + j
    -- (2) 1 * str.chars[X] = str.chars[X]  only at startIndex + j
    -- Σ_k  hot[k] * str.chars[k + j] = str.chars[startIndex + j]
    let extracted : F p ← share $ (List.finRange maxStrLen).foldl (fun sum (k : Fin maxStrLen) ↦
      if h : k.val + j.val < maxStrLen then
        sum + (convert hot[k]) * str.chars[k.val + j.val].toF
      else
        sum
    ) (const 0)
    -- Compare extracted value with substr char
    let matched ← isZero (extracted - substr.chars[j].toF)
    -- position beyond substr.len → automatically true:
    -- If this position is part of the substring, check the match. If it's padding, skip it (always true)
    let gated := FB.or (FB.not substrSel[j]) matched
    return FB.and acc gated
  ) FB.true
  return success

/-- Asserts that `substr` appears in `str` starting at `startIndex`. -/
def assertIsSubstring {maxStrLen maxSubstrLen : ℕ} (str : FString p maxStrLen) (substr : FString p maxSubstrLen) (startIndex : F p) : Option Unit := do
  FB.assert (← isSubstring str substr startIndex)

variable [Core Primes.bn254]

open Primes HashToField in
/--
  Fiat-Shamir variant of `isSubstring`.
  Specialised to `Primes.bn254` because Poseidon constants are bn254-only.

  `strHash` is the pre-computed hash of `str` (i.e., `hashBytesToFieldWithLen str.chars str.len`).
  This is taken as a parameter to avoid re-hashing when repeatedly calling this template on the
  same string.
-/
def isSubstringFS {maxStrLen maxSubstrLen : ℕ} (_h : maxSubstrLen ≤ maxStrLen)
    (str        : FString bn254 maxStrLen)
    (strHash    : F bn254)
    (substr     : FString bn254 maxSubstrLen)
    (startIndex : F bn254)
    : Option (FB bn254) := do
  -- Step 1: hash substr and derive the random challenge α
  let substrHash ← hashBytesToFieldWithLen (substr.chars.map FBitVec.toF) substr.len
  -- random_challenge = H(str_hash, substr_hash, substr_len, start_index)
  let α ← Clap.Poseidon.poseidonBN254 [strHash, substrHash, substr.len, startIndex]
  -- Step 2: build challenge powers α⁰, α¹, …, α^{maxStrLen-1}
  -- powers[0] = 1, powers[i] = α^i
  let powers : Vector (F bn254) maxStrLen :=
    Vector.ofFn (fun i ↦ (List.iterate (fun x ↦ share (x * α)) (const (1 : ZMod bn254)) (i.val + 1)).getLast!)
  -- Step 3: selector bits for [startIndex, startIndex + substr.len)
  let selector ← FArray.arraySelector maxStrLen startIndex (startIndex + substr.len)
  -- Step 4: selected_str[i] = selector[i] * str[i]; ŝ(α) = Σᵢ selected_str[i] · powers[i]
  let mut strPolyEval : F bn254 := const 0
  for l : i in [0:maxStrLen] do
    strPolyEval := strPolyEval + (convert selector[i]) * str.chars[i].toF * powers[i]
  -- Step 5: t(α) = Σⱼ substr[j] · powers[j]
  let mut substrPolyEval : F bn254 := const 0
  for l : j in [0:maxSubstrLen] do
    substrPolyEval := substrPolyEval + substr.chars[j].toF * powers[j]!
  -- Step 6: α^startIndex = SelectArrayValue(powers, startIndex)
  let distinguishingValue ← FArray.selectArrayValue powers startIndex
  -- Step 7: success = NOT(isZero(ŝ(α))) AND isEqual(ŝ(α), α^startIndex · t(α))
  let nonZero : FB bn254 := FB.not (isZero (share strPolyEval))
  let polyEq  : FB bn254 := isZero (strPolyEval - distinguishingValue * substrPolyEval)
  return FB.and nonZero polyEq

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
  - `right` is 0-padded after `right.len` characters
  - `fullStr = left || right` where `||` is concatenation
-/
def assertIsConcatenation
    {maxFullLen maxLeftLen maxRightLen : ℕ}
    (_hl : maxLeftLen ≤ maxFullLen) (_hr : maxRightLen ≤ maxFullLen)
    (fullStr : FString bn254 maxFullLen)
    (left    : FString bn254 maxLeftLen)
    (right   : FString bn254 maxRightLen)
    : Option Unit := do
  -- Step 1: hash all three strings and derive the random challenge
  let leftHash  ← hashBytesToFieldWithLen (left.chars.map FBitVec.toF) left.len
  let rightHash ← hashBytesToFieldWithLen (right.chars.map FBitVec.toF) right.len
  let fullHash  ← hashBytesToFieldWithLen (fullStr.chars.map FBitVec.toF) (left.len + right.len)
  let α ← Clap.Poseidon.poseidonBN254 [leftHash, rightHash, fullHash, left.len]
  -- Step 2: enforce that left is 0-padded after left.len
  -- rightArraySelector(left_len - 1) gives 1s at positions > left_len - 1, i.e. at [left_len, maxLeftLen)
  let leftSelector ← FArray.rightArraySelector maxLeftLen (left.len - const 1)
  for l : i in [0:maxLeftLen] do
    eq0 ((convert leftSelector[i]) * left.chars[i].toF)
  -- Step 2b: enforce that right is 0-padded after right.len
  let rightSelector ← FArray.rightArraySelector maxRightLen (right.len - const 1)
  for l : i in [0:maxRightLen] do
    eq0 ((convert rightSelector[i]) * right.chars[i].toF)
  -- Step 3: build challenge powers α⁰, α¹, …, α^{maxFullLen-1}
  let powers : Vector (F bn254) maxFullLen :=
    Vector.ofFn (fun i ↦ (List.iterate (fun x ↦ share (x * α)) (const (1 : ZMod bn254)) (i.val + 1)).getLast!)
  -- Step 4: left_poly_eval = Σᵢ left[i] · powers[i]
  let mut leftPolyEval : F bn254 := const 0
  for l : i in [0:maxLeftLen] do
    leftPolyEval := leftPolyEval + left.chars[i].toF * powers[i]!
  -- Step 5: right_poly_eval = Σⱼ right[j] · powers[j]
  let mut rightPolyEval : F bn254 := const 0
  for l : j in [0:maxRightLen] do
    rightPolyEval := rightPolyEval + right.chars[j].toF * powers[j]!
  -- Step 6: full_poly_eval = Σₖ fullStr[k] · powers[k]
  let mut fullPolyEval : F bn254 := const 0
  for l : k in [0:maxFullLen] do
    fullPolyEval := fullPolyEval + fullStr.chars[k].toF * powers[k]
  -- Step 7: distinguishing_value = α^left_len = SelectArrayValue(powers, left_len)
  let distinguishingValue ← FArray.selectArrayValue powers left.len
  -- Step 8: assert full_poly_eval = left_poly_eval + α^left_len · right_poly_eval
  F.assert_eq fullPolyEval (leftPolyEval + distinguishingValue * rightPolyEval)

end FString

namespace TestString

open Clap.Lang Core Clap.Spec ZMod
open FChar FString

abbrev p := Primes.goldilocks

instance onlyForDebugF {p : ℕ} : ToString (ZMod p) where
  toString f := Clap.natToHex f.val

scoped instance instCoreZMod (p : ℕ) [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : Core p where
  F := ZMod p
  FB := ZMod p
  convert := id
  const := id
  accept := Compiler.accept
  eq0 := Compiler.eq0
  share := Compiler.share
  shareB := Compiler.share
  isZero := Compiler.is_zero
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num
  onlyForDebugF
  onlyForDebugFB := onlyForDebugF

-- isWhitespace tests
example : FChar.isWhitespace (F8.ofF! (p := p) 9)  = some FB.true := by native_decide -- TAB
example : FChar.isWhitespace (F8.ofF! (p := p) 10) = some FB.true := by native_decide -- LF
example : FChar.isWhitespace (F8.ofF! (p := p) 11) = some FB.true := by native_decide -- VT
example : FChar.isWhitespace (F8.ofF! (p := p) 12) = some FB.true := by native_decide -- FF
example : FChar.isWhitespace (F8.ofF! (p := p) 13) = some FB.true := by native_decide -- CR
example : FChar.isWhitespace (F8.ofF! (p := p) 32) = some FB.true := by native_decide -- SPACE
example : FChar.isWhitespace (F8.ofF! (p := p) 65) = some FB.false := by native_decide -- 'A'
example : FChar.isWhitespace (F8.ofF! (p := p) 0)  = some FB.false := by native_decide -- NUL

-- helpers
private def ch (n : ℕ) : FChar p := F8.ofF! n
/-- Construct an `FString` from a char vector and a length for use in tests. -/
private def mkFStr (n : ℕ) (chars : Vector (FChar p) n) (len : F p) : FString p n := ⟨chars, len⟩

-- assertIsAsciiDigits tests
example : FString.assertIsAsciiDigits (p := p) (mkFStr 3 (#v[48, 57, 0].map ch)   2) = some () := by native_decide
example : FString.assertIsAsciiDigits (p := p) (mkFStr 3 (#v[48, 49, 50].map ch)  3) = some () := by native_decide
example : FString.assertIsAsciiDigits (p := p) (mkFStr 3 (#v[48, 49, 100].map ch) 2) = some () := by native_decide -- non-digit after len OK
example : FString.assertIsAsciiDigits (p := p) (mkFStr 3 (#v[47, 48, 0].map ch)   2) = none := by native_decide    -- '/'=47 below '0'
example : FString.assertIsAsciiDigits (p := p) (mkFStr 3 (#v[48, 58, 0].map ch)   2) = none := by native_decide    -- ':'=58 above '9'

-- asciiDigitsToScalar tests
-- ASCII digit mapping: '0'=48 '1'=49 '2'=50 '3'=51 '4'=52 '5'=53 '6'=54 '7'=55 '8'=56 '9'=57
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[55, 0, 0].map ch) 1) = some 7 := by native_decide            -- "7"     → 7
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[49, 50, 0].map ch) 2) = some 12 := by native_decide          -- "12"    → 12
example : FString.asciiDigitsToScalar (p := p) (mkFStr 4 (#v[49, 50, 51, 0].map ch) 3) = some 123 := by native_decide  -- "123"   → 123
example : FString.asciiDigitsToScalar (p := p) (mkFStr 6 (#v[49, 50, 51, 52, 53, 0].map ch) 5) = some 12345 := by native_decide -- "12345" → 12345
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[48, 0, 0].map ch) 1) = some 0 := by native_decide            -- "0"     → 0
example : FString.asciiDigitsToScalar (p := p) (mkFStr 4 (#v[51, 48, 53, 0].map ch) 3) = some 305 := by native_decide  -- "305"   → 305 ('3'=51 '0'=48 '5'=53)
example : FString.asciiDigitsToScalar (p := p) (mkFStr 5 (#v[57, 56, 55, 54, 0].map ch) 4) = some 9876 := by native_decide -- "9876"  → 9876 ('9'=57 '8'=56 '7'=55 '6'=54)
example : FString.asciiDigitsToScalar (p := p) (mkFStr 4 (#v[52, 50, 100, 100].map ch) 2) = some 42 := by native_decide -- "42"    → 42 (non-digit padding beyond len ignored)
-- do we want this behaviour?
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[49, 50, 51].map ch) 3) = none := by native_decide            -- len = maxLen: no index_eq fires
example : FString.asciiDigitsToScalar (p := p) (mkFStr 4 (#v[57, 56, 55, 54].map ch) 4) = none := by native_decide     -- len = maxLen: digits valid but out of range
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[49, 50, 51].map ch) 0) = none := by native_decide            -- len = 0: arraySelector rejects
example : FString.asciiDigitsToScalar (p := p) (mkFStr 1 (#v[55].map ch) 1) = none := by native_decide                          -- maxLen = 1: fold empty, ieq_sum stays 0
example : FString.asciiDigitsToScalar (p := p) (mkFStr 3 (#v[65, 49, 0].map ch) 2) = none := by native_decide             -- "A1": 'A'=65 not a digit, assertIsAsciiDigits fails

-- isSubstring tests
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'a'=97 'b'=98 'c'=99 'x'=120 'y'=121 'z'=122

-- "hel" in "hello" at 0
example : FString.isSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[104, 101, 108].map ch) 3) 0 = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : FString.isSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[101, 108, 108].map ch) 3) 1 = some FB.true := by native_decide

-- "xyz" in "hello" at 0 (no match)
example : FString.isSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[120, 121, 122].map ch) 3) 0 = some FB.false := by native_decide

-- "lo" in "hello" at 3
example : FString.isSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 2 (#v[108, 111].map ch) 2) 3 = some FB.true := by native_decide

-- Substr extends beyond str → false: "lo" in "hello" at 4
example : FString.isSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[108, 111, 0].map ch) 2) 4 = some FB.false := by native_decide

-- "b" in "abc" at 1
example : FString.isSubstring (p := p)
  (mkFStr 3 (#v[97, 98, 99].map ch) 3)
  (mkFStr 1 (#v[98].map ch) 1) 1 = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : FString.assertIsSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[101, 108, 108].map ch) 3) 1 = some () := by native_decide

-- assertIsSubstring failure: "xyz" in "hello" at 0
example : FString.assertIsSubstring (p := p)
  (mkFStr 5 (#v[104, 101, 108, 108, 111].map ch) 5)
  (mkFStr 3 (#v[120, 121, 122].map ch) 3) 0 = none := by native_decide

-- isSubstringFS tests (bn254-only due to Poseidon)
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'a'=97 'b'=98 'c'=99 'x'=120 'y'=121 'z'=122

abbrev q := Primes.bn254

private def chq (n : ℕ) : FChar q := F8.ofF! n
private def mkFStrQ (n : ℕ) (chars : Vector (FChar q) n) (len : F q) : FString q n := ⟨chars, len⟩

/-- Compute `strHash` for an `FString` via `hashBytesToFieldWithLen`. -/
private def strHashOf {n : ℕ} (s : FString q n) : Option (F q) :=
  HashToField.hashBytesToFieldWithLen (s.chars.map FBitVec.toF) s.len

-- "hel" in "hello" at 0
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 3 (#v[104, 101, 108].map chq) 3) 0
  ) = some FB.true := by native_decide

-- "ell" in "hello" at 1
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 3 (#v[101, 108, 108].map chq) 3) 1
  ) = some FB.true := by native_decide

-- "xyz" in "hello" at 0 (no match)
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 3 (#v[120, 121, 122].map chq) 3) 0
  ) = some FB.false := by native_decide

-- "lo" in "hello" at 3
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 2 (#v[108, 111].map chq) 2) 3
  ) = some FB.true := by native_decide

-- Substr extends beyond str → false: "lo" in "hello" at 4
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 3 (#v[108, 111, 0].map chq) 2) 4
  ) = some FB.false := by native_decide

-- "b" in "abc" at 1
example : (do
  let str := mkFStrQ 3 (#v[97, 98, 99].map chq) 3
  let h ← strHashOf str
  FString.isSubstringFS (by omega) str h (mkFStrQ 1 (#v[98].map chq) 1) 1
  ) = some FB.true := by native_decide

-- assertIsSubstringFS: "ell" in "hello" at 1
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.assertIsSubstringFS (by omega) str h (mkFStrQ 3 (#v[101, 108, 108].map chq) 3) 1
  ) = some () := by native_decide

-- assertIsSubstringFS failure: "xyz" in "hello" at 0
example : (do
  let str := mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5
  let h ← strHashOf str
  FString.assertIsSubstringFS (by omega) str h (mkFStrQ 3 (#v[120, 121, 122].map chq) 3) 0
  ) = none := by native_decide

-- assertIsConcatenation tests
-- ASCII: 'h'=104 'e'=101 'l'=108 'o'=111 'w'=119 'r'=114 'd'=100 'a'=97 'b'=98 'c'=99

-- 1. "hello" = "hel" ++ "lo" (basic concatenation)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5)
  (mkFStrQ 3 (#v[104, 101, 108].map chq) 3)
  (mkFStrQ 2 (#v[108, 111].map chq) 2)
  = some () := by native_decide

-- 2. "hello" = "h" ++ "ello" (split at 1)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 5 (#v[104, 101, 108, 108, 111].map chq) 5)
  (mkFStrQ 1 (#v[104].map chq) 1)
  (mkFStrQ 4 (#v[101, 108, 108, 111].map chq) 4)
  = some () := by native_decide

-- 3. "abc" = "ab" ++ "c" (different string)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  (mkFStrQ 2 (#v[97, 98].map chq) 2)
  (mkFStrQ 1 (#v[99].map chq) 1)
  = some () := by native_decide

-- 4. maxLen > actual len with 0-padding: full="ab\0" (len=2) = "a\0" (len=1) ++ "b\0" (len=1)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 0].map chq) 2)
  (mkFStrQ 2 (#v[97, 0].map chq) 1)
  (mkFStrQ 2 (#v[98, 0].map chq) 1)
  = some () := by native_decide

-- 5. Wrong concatenation: "abc" ≠ "ab" ++ "b" (right doesn't match)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  (mkFStrQ 2 (#v[97, 98].map chq) 2)
  (mkFStrQ 1 (#v[98].map chq) 1)
  = none := by native_decide

-- 6. Wrong concatenation: "abc" ≠ "ac" ++ "c" (left doesn't match)
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  (mkFStrQ 2 (#v[97, 99].map chq) 2)
  (mkFStrQ 1 (#v[99].map chq) 1)
  = none := by native_decide

-- 7a. Left 0-padding valid: left = [97, 98, 0] with len=2 passes
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  -- len=2, byte at index 2 is 0 → valid padding
  (mkFStrQ 3 (#v[97, 98, 0].map chq) 2) (mkFStrQ 1 (#v[99].map chq) 1)
  = some () := by native_decide

-- 7b. Left 0-padding violated: left = [97, 98, 99] with len=2 fails
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  -- len=2, byte at index 2 is non-zero → fails
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 2) (mkFStrQ 1 (#v[99].map chq) 1)
  = none := by native_decide

-- 8a. Right 0-padding valid: right = [99, 0] with len=1 passes
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  -- len=1, byte at index 1 is 0 → valid padding
  (mkFStrQ 2 (#v[97, 98].map chq) 2) (mkFStrQ 2 (#v[99, 0].map chq) 1)
  = some () := by native_decide

-- 8b. Right 0-padding violated: right = [99, 100] with len=1 fails
example : FString.assertIsConcatenation (by omega) (by omega)
  (mkFStrQ 3 (#v[97, 98, 99].map chq) 3)
  -- len=1, byte at index 1 is non-zero → fails
  (mkFStrQ 2 (#v[97, 98].map chq) 2) (mkFStrQ 2 (#v[99, 100].map chq) 1)
  = none := by native_decide

end TestString
