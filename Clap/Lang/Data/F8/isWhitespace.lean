import Clap.Lang.Data.F8.F8
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.or
namespace Clap.Lang.F8

variable {p : ℕ}

/-- ASCII whitespace: TAB(9), LF(10), VT(11), FF(12), CR(13), or SPACE(32). -/
def isWhitespace [p.AtLeastTwo] (c : F8 p) : ClapM p (FB p) := do
  let eight     ← mkF 8
  let fourteen  ← mkF 14
  let thirtytwo ← mkF 32
  let isLineBreak ← FB.and (← greaterThan c eight) (← lessThan c fourteen)
  let isSpace     ← eq c thirtytwo
  FB.or isLineBreak isSpace

namespace isWhitespace

lemma convertsM [p.AtLeastTwo] {state}
  {e : F8 p}
  {e_val : UInt8}
  (hp : 2^(8+1) < p)
  (h_e : Converts F8.conversion state e e_val)
  :
  ConvertsM FB.conversion
    (isWhitespace e)
    state
    (e_val > 8 && e_val < 14 || e_val = 32)
    True
  := by
  have hp' : (512 : ℕ) < p := by norm_num at hp; omega
  have h_e_f := F.converts_of_F8_converts h_e
  have h_toNat_lt : e_val.toNat < 256 := e_val.toNat_lt_size
  have h_toNat_p : e_val.toNat < p := by omega
  have h8p : (8 : ℕ) < p := by omega
  have h14p : (14 : ℕ) < p := by omega
  have h32p : (32 : ℕ) < p := by omega
  have hve : (e_val.toNat : ZMod p).val = e_val.toNat := ZMod.val_natCast_of_lt h_toNat_p
  have hv8 : (8 : ZMod p).val = 8 := ZMod.val_ofNat_of_lt h8p
  have hv14 : (14 : ZMod p).val = 14 := ZMod.val_ofNat_of_lt h14p
  have hv32 : (32 : ZMod p).val = 32 := ZMod.val_ofNat_of_lt h32p
  unfold isWhitespace greaterThan lessThan eq Clap.Lang.greaterThan
  step mkF.convertsM as eight
  step mkF.convertsM as fourteen
  step mkF.convertsM as thirtytwo
  step Clap.Lang.lessThan.convertsM h_eight h_e_f (by rw [hv8]; omega) (by rw [hve]; omega) hp as gt8
  step Clap.Lang.lessThan.convertsM h_e_f h_fourteen (by rw [hve]; omega) (by rw [hv14]; omega) hp as lt14
  step FB.and.convertsM h_gt8 h_lt14 as isLineBreak
  step Clap.Lang.eq.convertsM h_e_f h_thirtytwo as isSpace
  apply convertsM_of_convertsM (FB.or.convertsM h_isLineBreak h_isSpace)
  · rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hv8, hve, hv14,
        show ((e_val.toNat : ZMod p) = (32 : ZMod p)) ↔ e_val.toNat = 32 from by
          rw [← (ZMod.val_injective p).eq_iff, hve, hv32],
        show (e_val > (8 : UInt8)) ↔ (8 : ℕ) < e_val.toNat from Iff.rfl,
        show (e_val < (14 : UInt8)) ↔ e_val.toNat < (14 : ℕ) from Iff.rfl,
        show (e_val = (32 : UInt8)) ↔ e_val.toNat = (32 : ℕ) from by
          rw [← UInt8.toNat_inj]; rfl]
  · trivial

/-- The range-check characterisation of whitespace agrees with the explicit character-set one. -/
lemma isWhitespace_eq_isWhitespace_high (e_val : UInt8) :
    (e_val > 8 && e_val < 14 || e_val = 32) =
    (decide (e_val ∈ [ '\t', '\n', '\x0B', '\x0C', '\x0D', ' ' ].map Char.toUInt8) : Bool)
:= by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  rw [show e_val ∈
        [ '\t', '\n', '\x0B', '\x0C', '\x0D', ' ' ].map Char.toUInt8 ↔
        (e_val = 9 ∨ e_val = 10 ∨ e_val = 11 ∨ e_val = 12 ∨ e_val = 13 ∨ e_val = 32) from by
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨c, hc, rfl⟩
        rcases hc with h | h | h | h | h | h <;> subst h <;> decide
      · rintro (h | h | h | h | h | h) <;> subst h
        · exact ⟨'\t', by tauto, by decide⟩
        · exact ⟨'\n', by tauto, by decide⟩
        · exact ⟨'\x0B', by tauto, by decide⟩
        · exact ⟨'\x0C', by tauto, by decide⟩
        · exact ⟨'\x0D', by tauto, by decide⟩
        · exact ⟨' ', by tauto, by decide⟩,
      show (e_val > (8 : UInt8)) ↔ (8 : ℕ) < e_val.toNat from Iff.rfl,
      show (e_val < (14 : UInt8)) ↔ e_val.toNat < (14 : ℕ) from Iff.rfl,
      show (e_val = (9 : UInt8)) ↔ e_val.toNat = (9 : ℕ) from by rw [← UInt8.toNat_inj]; rfl,
      show (e_val = (10 : UInt8)) ↔ e_val.toNat = (10 : ℕ) from by rw [← UInt8.toNat_inj]; rfl,
      show (e_val = (11 : UInt8)) ↔ e_val.toNat = (11 : ℕ) from by rw [← UInt8.toNat_inj]; rfl,
      show (e_val = (12 : UInt8)) ↔ e_val.toNat = (12 : ℕ) from by rw [← UInt8.toNat_inj]; rfl,
      show (e_val = (13 : UInt8)) ↔ e_val.toNat = (13 : ℕ) from by rw [← UInt8.toNat_inj]; rfl,
      show (e_val = (32 : UInt8)) ↔ e_val.toNat = (32 : ℕ) from by rw [← UInt8.toNat_inj]; rfl]
  omega

lemma convertsM_high [p.AtLeastTwo] {state}
  {e : F8 p}
  {e_val : UInt8}
  (hp : 2^(8+1) < p)
  (h_e : Converts F8.conversion state e e_val)
  :
  ConvertsM FB.conversion
    (isWhitespace e)
    state
    (e_val ∈
      [ '\t',   -- tab
        '\n',   -- line feed
        '\x0B', -- \∨ vertical tab
        '\x0C', -- \f form feed
        '\x0D', -- \r carriage return
        ' '
        ].map Char.toUInt8
    )
    True
:= by
  apply convertsM_of_convertsM (convertsM hp h_e)
  · exact isWhitespace_eq_isWhitespace_high e_val
  · trivial

end isWhitespace

end Clap.Lang.F8
