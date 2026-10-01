import Clap.Lang.Gate.num2bits
import Clap.Model.Convert.PaddedVector
import Clap.Util.Wheels
-- import Clap.Lang.Core.FB.ofBool
-- import Clap.Lang.Core.F.mkAdd
-- import Clap.Lang.Core.F.mkSub
-- import Clap.Lang.Core.F.lessThan
-- import Clap.Lang.Core.FB.and
-- import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FBitVec.bits2numV
import Clap.Lang.Data.Base64Len.base64UrlLookup
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

namespace base64UrlDecode

/-- Get the base64URL index of a char -/
private def charIndex (c : Char) : ℕ :=
  if c.isUpper then (c.toNat - 'A'.toNat)
  else if c.isLower then (c.toNat - 'a'.toNat + 26)
  else if c.isDigit then (c.toNat - '0'.toNat + 52)
  else if c == '-' then 62
  else if c == '_' then 63
  else 0

/-- Get the base64URL index of a char, in binary form. -/
private def charIndexBin (c : Char) : List Bool :=
  let bs := (charIndex c : BitVec 6)
  Vector.ofFn (fun i => bs.getMsb i) |>.toList

/-- Base64URL decode. Not expected to work with '=' padding -/
def decode (encoded : String) : String :=
  let bits₀ := encoded.toList.map charIndexBin
  let bits₁ := bits₀.flatten
  let bits₂ := bits₁.toChunks 8
  let toNatMSB (bs : List Bool) := bs.foldl (fun acc b => 2 * acc + b.toNat) 0
  let e₄ := bits₂.map toNatMSB
  String.ofList (e₄.map Char.ofNat)

#guard decode "TWFu" == "Man"

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a : FString p (w * 4 / 3)}
  {a_val : String}
  (h_a : Converts FString.conversion state a a_val)
  (h_len : 3 ∣ w)
  (h_a_len : a_val.length = w * 4 / 3)
  (h_p : 2 ^ (8 + 1) < p)
:
  ConvertsM FString.conversion (base64UrlDecode h_len a) state
    (decode a_val)
    (a_val.toList.all
      fun c ↦ c ∈ [Char.ofNat 0, '-', '_', '='] ∨ c.isUpper ∨ c.isLower ∨ c.isDigit
    )
:= by

  sorry

end base64UrlDecode
