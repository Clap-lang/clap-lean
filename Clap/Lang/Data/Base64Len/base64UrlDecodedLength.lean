import Clap.Lang.Gate.num2bits
import Clap.Lang.Gate.share
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Data.FArray.bits2num

namespace Clap.Lang.Base64

variable {p : ℕ}

/--
Returns the length of the decoded data, given a base64url (unpadded) encoded length `m`.

length = floor{3 * encoded length / 4}
-/
def base64UrlDecodedLength (w : ℕ) (m : F p) : ClapM p (F p) := do
  let _ ← num2bits w m -- range-check m < 2^w
  let twice ← share (← m + m)
  let threeTimes : F p ← share (←(twice + m))
  let bits ← num2bits (w + 2) threeTimes -- decompose 3m, proves < 2^(w+2)
  FArray.bits2num (bits.drop 2) -- drop 2 LSBs = floor(3m/4)

namespace base64UrlDecodedLength

lemma convertsM {w}
  {state : ClapMState p}
  {m : F p}
  {m_val : ZMod p}
  (h_m : Converts F.conversion state m m_val)
  (h_range : m_val.val < 2 ^ w)
  (h_field : 2 ^ (w + 2) ≤ p)
:
  ConvertsM F.conversion (base64UrlDecodedLength w m) state
    (OfNat.ofNat <| 3*m_val.val/4)
    (m_val.val < 2 ^ w ∧ 3 * m_val.val < 2 ^ (w+2))
:= by
  have h_pow : (2 : ℕ) ^ (w + 2) = 2 ^ w * 4 := by rw [pow_add]; norm_num
  have h_3m_lt_pow : 3 * m_val.val < 2 ^ (w + 2) := by omega
  have h3m_lt_p : 3 * m_val.val < p := h_3m_lt_pow.trans_le h_field
  have h2m_lt_p : 2 * m_val.val < p := by omega
  have h_val2 : (m_val + m_val).val = 2 * m_val.val := by
    rw [ZMod.val_add_of_lt (by omega)]; ring
  have h_val3 : (m_val + m_val + m_val).val = 3 * m_val.val := by
    rw [ZMod.val_add_of_lt (by rw [h_val2]; omega), h_val2]; ring
  have h_2w_pos : 0 < (2 : ℕ) ^ w := pow_pos (by norm_num) w
  haveI : p.AtLeastTwo := ⟨by omega⟩
  unfold base64UrlDecodedLength
  step num2bits.convertsM h_m (w := w) as ignored
  step mkAdd.convertsM h_m h_m as sum1
  step share.convertsM h_sum1 as twice
  step mkAdd.convertsM h_twice h_m as sum2
  step share.convertsM h_sum2 as threeTimes
  step num2bits.convertsM h_threeTimes (w := w + 2) as bits
  · have h_bits_drop := FArray.converts_drop h_bits (n := 2)
    apply convertsM_of_convertsM (FArray.bits2num.convertsM h_bits_drop)
    · rw [FArray.toNum_eq_ofBoolListLE, Vector.toList_drop, Vector.toList_map, ofBoolListLE_drop_toNat,
        ← Vector.toList_map, ofBoolListLE_num2bitsLsbPureV_toNat, h_val3,
        Nat.mod_eq_of_lt h_3m_lt_pow]
      exact Eq.symm (Semiring.toGrindSemiring_ofNat (ZMod p) _)
    · exact iff_of_true trivial (fun _ _ _ _ _ h_r => ⟨h_r, h_3m_lt_pow⟩)
  · intro _; rw [h_val3]; exact h_3m_lt_pow

end base64UrlDecodedLength

end Clap.Lang.Base64
