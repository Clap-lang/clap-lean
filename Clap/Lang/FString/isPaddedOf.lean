import Clap.Lang.Combinators.ofFnM
import Clap.Lang.F.mkF
import Clap.Lang.F.ofChar
import Clap.Lang.FB.and
import Clap.Lang.FB.eq
import Clap.Lang.FString.Basic
import Clap.Lang.FVec.eq

namespace Clap.Lang.FString

variable {p : ℕ}

/--
Does `a` hold exactly the zero-padded encoding of the literal string `b`?
-/
def isPaddedOf [p.AtLeastTwo] {w : ℕ} (a : FString p w) (b : String) : ClapM p (FB p) := do
  let bData ← Vector.ofFnM (fun i : Fin w ↦
    if h : i.val < b.toList.length then ofChar (b.toList[i.val]'h) else mkF 0)
  let dataEq ← FVec.eq a.data bData
  let lenRef ← mkF (b.length : ZMod p)
  let lenEq ← _root_.Clap.Lang.eq a.len lenRef
  FB.and dataEq lenEq

namespace isPaddedOf

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a : FString p w}
  {a_val : String}
  {b : String}
  (h_a : Converts FString.conversion state a a_val)
:
  ConvertsM FB.conversion (isPaddedOf a b) state
    (decide (encodeV (p := p) w a_val = encodeV (p := p) w b) &&
      ((a_val.length : ZMod p) == (b.length : ZMod p))) True
:= by
  unfold isPaddedOf

  have h_pos : ∀ (i : Fin w) (state' : ClapMState p),
      ConvertsM F.conversion
        (if h : i.val < b.toList.length then ofChar (b.toList[i.val]'h) else mkF 0)
        state' ((encodeV w b)[i]) True := by
    intro i state'
    by_cases h : i.val < b.toList.length
    · have h_enc : (encodeV (p := p) w b)[i] =
          (((b.toList[i.val]'h).toUInt8.toNat : ℕ) : ZMod p) := by
        simp [encodeV, h]
      simp only [dif_pos h]
      rw [h_enc]
      exact ofChar.convertsM
    · have h_enc : (encodeV (p := p) w b)[i] = 0 := by simp [encodeV, h]
      simp only [dif_neg h]
      rw [h_enc]
      exact mkF.convertsM

  step (convertsM_ofFnM h_pos) as bData
  step (FVec.eq.convertsM (FString.converts_data h_a) h_bData) as dataEq
  step mkF.convertsM as lenRef
  step (_root_.Clap.Lang.eq.convertsM (FString.converts_len h_a) h_lenRef) as lenEq

  apply convertsM_of_convertsM (FB.and.convertsM h_dataEq h_lenEq)
  . rfl
  . trivial

section StringLevel

private lemma natCast_inj_of_lt {m n : ℕ} (hm : m < p) (hn : n < p)
    (h : (m : ZMod p) = (n : ZMod p)) : m = n := by
  haveI : NeZero p := ⟨by omega⟩
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at hv

private lemma toUInt8_toNat_of_lt {c : Char} (h : c.toNat < 256) :
    c.toUInt8.toNat = c.toNat := by
  show (c.val.toUInt8).toNat = c.val.toNat
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt h

private lemma char_ext_of_toNat {c d : Char} (h : c.toNat = d.toNat) : c = d :=
  Char.ext (UInt32.toNat.inj h)

private lemma encodeV_getElem_of_lt
    {w : ℕ} {s : String} {i : ℕ} (hi : i < w) (h : i < s.toList.length) :
    (encodeV (p := p) w s)[i]'hi = (((s.toList[i]'h).toUInt8.toNat : ℕ) : ZMod p) := by
  simp [encodeV, h]

/--
The encoding determines the string, given the side conditions the old model carried in
`Spec.FString.valid` and in `isPaddedOf_equiv`'s hypotheses.
-/
lemma encode_eq_iff
  {w : ℕ} {s t : String}
  (hs : s.length < w) (ht : t.length < w)
  (hsc : ∀ c ∈ s.toList, c.toNat < 256)
  (htc : ∀ c ∈ t.toList, c.toNat < 256)
  (hp : 256 < p) (hw : w < p)
:
  (encodeV (p := p) w s = encodeV (p := p) w t ∧
    ((s.length : ZMod p) = (t.length : ZMod p))) ↔ s = t
:= by
  constructor
  · rintro ⟨henc, hlen⟩
    have hlen' : s.length = t.length :=
      natCast_inj_of_lt (by omega) (by omega) hlen
    rw [← String.toList_inj]
    apply List.ext_getElem (by rw [String.length_toList, String.length_toList, hlen'])
    intro i hi_s hi_t
    have hi_w : i < w := by
      have h1 : i < s.toList.length := hi_s
      rw [String.length_toList] at h1
      omega
    have h_at : (encodeV (p := p) w s)[i]'hi_w = (encodeV (p := p) w t)[i]'hi_w := by
      rw [henc]
    rw [encodeV_getElem_of_lt hi_w hi_s, encodeV_getElem_of_lt hi_w hi_t] at h_at
    have hc_s : (s.toList[i]'hi_s).toNat < 256 := hsc _ (List.getElem_mem hi_s)
    have hc_t : (t.toList[i]'hi_t).toNat < 256 := htc _ (List.getElem_mem hi_t)
    have h_nat := natCast_inj_of_lt
      (m := (s.toList[i]'hi_s).toUInt8.toNat) (n := (t.toList[i]'hi_t).toUInt8.toNat)
      (by rw [toUInt8_toNat_of_lt hc_s]; omega)
      (by rw [toUInt8_toNat_of_lt hc_t]; omega)
      h_at
    rw [toUInt8_toNat_of_lt hc_s, toUInt8_toNat_of_lt hc_t] at h_nat
    exact char_ext_of_toNat h_nat
  · rintro rfl
    exact ⟨rfl, rfl⟩

lemma convertsM_string
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a : FString p w}
  {a_val : String}
  {b : String}
  (h_a : Converts FString.conversion state a a_val)
  (h_a_len : a_val.length < w)
  (h_b_len : b.length < w)
  (h_a_chars : ∀ c ∈ a_val.toList, c.toNat < 256)
  (h_b_chars : ∀ c ∈ b.toList, c.toNat < 256)
  (h_p : 256 < p)
  (h_w : w < p)
:
  ConvertsM FB.conversion (isPaddedOf a b) state (decide (a_val = b)) True
:= by
  apply convertsM_of_convertsM (convertsM h_a)
  · have h := encode_eq_iff (p := p) h_a_len h_b_len h_a_chars h_b_chars h_p h_w
    by_cases heq : a_val = b
    · subst heq; simp
    · simp only [heq, decide_false, Bool.and_eq_false_iff]
      by_cases h1 : encodeV (p := p) w a_val = encodeV (p := p) w b
      · right
        rw [beq_eq_false_iff_ne]
        intro h2
        exact heq (h.mp ⟨h1, h2⟩)
      · left
        simp [h1]
  · trivial

end StringLevel

end Clap.Lang.FString.isPaddedOf
