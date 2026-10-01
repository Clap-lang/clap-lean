import Clap.Lang.Gate.num2bits
import Clap.Model.Convert.PaddedVector
-- import Clap.Lang.Core.FB.ofBool
-- import Clap.Lang.Core.F.mkAdd
-- import Clap.Lang.Core.F.mkSub
-- import Clap.Lang.Core.F.lessThan
-- import Clap.Lang.Core.FB.and
-- import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FBitVec.bits2numV
-- import Clap.Lang.Data.Base64Len.base64UrlLookup
import Clap.Lang.Data.Base64Len.base64UrlDecodedLength

namespace Clap.Lang.Base64

variable {p : ℕ}

def base64UrlDecode₀ {w} (h:3 ∣ w) (input : FVec p (w*4/3)) : ClapM p (FVec p w)
:= do
  let tmp : Vector (FBitVec p 6) _ ← input.mapM (num2bits 6)
  let tmp : Vector (FBitVec p 6) _ := tmp.map Vector.reverse
  let tmp : FBitVec p (w*4/3 * 6) := tmp.flatten
  let tmp : Vector (FBitVec p 8) w :=
    have h : w*4/3 * 6 = w * 8 := by
      have h1 : w * 4 / 3 * 6 = w * 8 / 6 * 6 := by grind
      have h2 : w * 8 / 6 * 6 = w * 8 := by grind
      aesop (add safe [h1,h2,Nat.div_mul_cancel])
    toChunks 8 (h ▸ tmp)
  tmp.mapM (fun b ↦ FBitVec.bits2numV b.reverse)

def base64UrlDecode {w} [p.AtLeastTwo] (h:3 ∣ w) (input : FString p (w*4/3)) :
  ClapM p (FString p w)
:= do
  let lookedup ← input.data.mapM base64UrlLookup
  let payload ← base64UrlDecode₀ h lookedup
  let len ← base64UrlDecodedLength w input.len
  return ⟨payload, len⟩


-- Using https://github.com/predictable-machines/lean4-base64/blob/main/Base64/Decode.lean

private def charIndex (c : Char) : Option UInt8 :=
  if c >= 'A' && c <= 'Z' then some (c.toNat - 'A'.toNat).toUInt8
  else if c >= 'a' && c <= 'z' then some (c.toNat - 'a'.toNat + 26).toUInt8
  else if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat + 52).toUInt8
  else if c == '+' || c == '-' then some 62
  else if c == '/' || c == '_' then some 63
  else if c == '=' then some 0
  else none

/-- Decode a Base64 string to bytes.
    Accepts both standard (`+/`) and URL-safe (`-_`) alphabets.
    Tolerates whitespace (spaces, newlines, carriage returns).
    Returns `none` on invalid input. -/
def decode (encoded : String) : Option ByteArray := do
  let chars := encoded.toList.filter fun c =>
    c != ' ' && c != '\n' && c != '\r' && c != '\t'
  if chars.isEmpty then return ByteArray.empty
  -- Pad to multiple of 4 if needed (URL-safe inputs omit padding)
  let padded :=
    let r := chars.length % 4
    if r == 0 then chars
    else chars ++ List.replicate (4 - r) '='
  if padded.length % 4 != 0 then none
  let mut result := ByteArray.empty
  let mut i := 0
  while i < padded.length do
    let c0 ← charIndex padded[i]!
    let c1 ← charIndex padded[i + 1]!
    let c2Char := padded[i + 2]!
    let c3Char := padded[i + 3]!
    let c2 ← charIndex c2Char
    let c3 ← charIndex c3Char
    result := result.push ((c0 <<< 2) ||| (c1 >>> 4))
    if c2Char != '=' then
      result := result.push (((c1 &&& 0x0F) <<< 4) ||| (c2 >>> 2))
    if c3Char != '=' then
      result := result.push (((c2 &&& 0x03) <<< 6) ||| c3)
    i := i + 4
  return result

/-- Decode a Base64 string and interpret the result as UTF-8.
    Returns `none` if the input is invalid Base64 or the decoded bytes
    are not valid UTF-8. -/
def decodeString (encoded : String) : Option String := do
  let bytes ← decode encoded
  String.fromUTF8? bytes

private def charIndex' (c : Char) : BitVec 8 :=
  if c.isUpper then Fin.ofNat 8 (c.toNat - 'A'.toNat)
  else if c.isLower then Fin.ofNat 8 (c.toNat - 'a'.toNat + 26)
  else if c.isDigit then Fin.ofNat 8 (c.toNat - '0'.toNat + 52)
  else if c == '-' then 62
  else if c == '_' then 63
  else 0

def decode' (encoded : String) : String :=
  let e₁ := encoded.toList.map charIndex'
  -- let e₂ := e₁.map (num2bitsLsbPureV 6
  sorry

#check "TWFu".toList.map charIndex'
#check charIndex' 'A'
#eval charIndex' 'T'
