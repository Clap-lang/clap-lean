import Clap.Lang.Gate.num2bits
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FBitVec.bits2numV

namespace Clap.Lang.Base64

variable {p : ℕ}

def base64UrlLookup [p.AtLeastTwo] (i : F p) : ClapM p (F p) := do
  -- check if i ∈ ['A', 'Z']
  let ge_A ← greaterEqThan 8 i (← mkF 'A'.toNat)
  let le_Z ← lessEqThan 8 i (← mkF 'Z'.toNat)
  let range_AZ ← ge_A.and le_Z
  let sixtyFive ← mkF 65
  let sum_AZ : F p ← mkMul (range_AZ : F p) (← mkSub i sixtyFive)

  -- check if i ∈ ['a', 'z']
  let ge_a ← greaterEqThan 8 i (← mkF 'a'.toNat)
  let le_z ← lessEqThan 8 i (← mkF 'z'.toNat)
  let range_az ← ge_a.and le_z
  let seventyOne ← mkF 71
  let diff ← mkSub i seventyOne
  let sum_az ← mkAdd sum_AZ (← mkMul (range_az : F p) diff)

  -- check if i ∈ ['0', '9']
  let ge_a ← greaterEqThan 8 i (← mkF '0'.toNat)
  let le_z ← lessEqThan 8 i (← mkF '9'.toNat)
  let range_09 ← ge_a.and le_z
  let four ← mkF 4
  let sum_09 ← mkAdd sum_az (← mkMul (range_09 : F p) (← mkAdd i four))

  -- check if i is '-'
  let eq_minus ← eq i (← mkF '-'.toNat)
  let sixtyTwo ← mkF 62
  let sum_minus ← mkAdd sum_09 (← mkMul (eq_minus : F p) sixtyTwo)

  -- check if i is '_'
  let eq_underscore ← eq i (← mkF '_'.toNat)
  let sixtyThree ← mkF 63
  let sum_underscore ← mkAdd sum_minus (← mkMul (eq_underscore : F p) sixtyThree)

  -- check if i is '='
  let eq_eqsign ← eq i (← mkF '='.toNat)

  -- check if i is zero
  let zero_padding ← isZero i

  -- exactly one case has to be true
  let sum ←
    [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
    |> List.foldrM mkAdd (←mkF 0)

  eq0 (← sum - (← mkF 1))
  pure sum_underscore

namespace base64UrlLookup

lemma convertsM [p.AtLeastTwo]
  {state : ClapMState p}
  {m : F p}
  {m_val : ZMod p}
  (h_m : Converts F.conversion state m m_val)
  (h_byte : m_val.val < 2^8)
  (h_p : 2^(8+1) < p)
:
  ConvertsM F.conversion (base64UrlLookup m) state
    (if (Char.ofNat m_val.val).isUpper then m_val - 65 else
      if (Char.ofNat m_val.val).isLower then m_val - 71 else
        if (Char.ofNat m_val.val).isDigit then m_val + 4 else
          if m_val.val == '-'.toNat then 62 else
            if m_val.val == '_'.toNat then 63 else 0
    )
    ( m_val.val ∈
      [0, '-'.toNat, '_'.toNat, '='.toNat] ++
      List.range' 'A'.toNat 26 ++
      List.range' 'a'.toNat 26 ++
      List.range' '0'.toNat 10
    )
:= by
  sorry

end base64UrlLookup

end Clap.Lang.Base64
