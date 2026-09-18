import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.ofChar
import Clap.Model.Convert.PaddedVector

namespace Clap.Lang.FString

variable {p : ℕ}

/--
A constant `FString`.
-/
def ofString {w : ℕ} (s : String) : ClapM p (FString p w) := do
  let data ← Vector.ofFnM (fun i : Fin w ↦
    if h : i.val < s.toList.length then ofChar (s.toList[i.val]'h) else mkF 0)
  let len ← mkF (s.length : ZMod p)
  return { data, len }

namespace ofString

lemma convertsM
  {w : ℕ}
  {s : String}
  {state : ClapMState p}
:
  ConvertsM FString.conversion (ofString (p := p) (w := w) s) state s True
:= by
  unfold ofString

  have h_pos : ∀ (i : Fin w) (state' : ClapMState p),
      ConvertsM F.conversion
        (if h : i.val < s.toList.length then ofChar (s.toList[i.val]'h) else mkF 0)
        state' ((encodeV w s)[i]) True := by
    intro i state'
    by_cases h : i.val < s.toList.length
    · have h_enc : (encodeV (p := p) w s)[i] =
          (((s.toList[i.val]'h).toUInt8.toNat : ℕ) : ZMod p) := by
        simp [encodeV, h]
      simp only [dif_pos h]
      rw [h_enc]
      exact ofChar.convertsM
    · have h_enc : (encodeV (p := p) w s)[i] = 0 := by simp [encodeV, h]
      simp only [dif_neg h]
      rw [h_enc]
      exact mkF.convertsM

  step (convertsM_ofFnM h_pos) as data
  step mkF.convertsM as len

  apply convertsM_pure
  . exact FString.converts_intro h_data h_len
  . trivial

end Clap.Lang.FString.ofString
