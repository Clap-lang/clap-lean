import Clap.Model.Convert.Specialised

/-!
# Strings behind a fixed-length representation

a string is encoded as one field element per character (its low byte), zero-padded
out to `w`, followed by the length.

Caveat: the encoding truncates at `w`, so it is injective only on strings shorter
than `w` whose characters fit in a byte, with `2^8 < p` and `w < p`. Gadgets that need
injectivity take those as explicit hypotheses. the `Converts` relation itself does not.
-/

namespace Clap.Lang

variable {p : ℕ}

/-- A fixed-width vector of `α` carrying a circuit-level length, so that a variable-length
value can be represented at a fixed width. Polymorphic in the element type: `FString` fills it
with field elements, while the keyless JWT inputs also use `PaddedVector (FB p) p w` for
per-character bit flags. -/
structure PaddedVector (α : Type) (p w : ℕ) where
  data : Vector α w
  len : F p

abbrev FString (p w : ℕ) := PaddedVector (F p) p w

namespace FString

/-- The characters of `s`, low byte each, zero-padded to `w`. -/
def encodeV (w : ℕ) (s : String) : Vector (ZMod p) w :=
  Vector.ofFn (fun i : Fin w ↦
    if h : i.val < s.toList.length then ((s.toList[i.val]'h).toUInt8.toNat : ZMod p) else 0)

/-- A character below 256 is its own low byte. -/
lemma toUInt8_toNat_of_lt {c : Char} (h : c.toNat < 256) :
    c.toUInt8.toNat = c.toNat := by
  show (c.val.toUInt8).toNat = c.val.toNat
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt h

lemma encodeV_getElem_of_lt
    {w : ℕ} {s : String} {i : ℕ} (hi : i < w) (h : i < s.toList.length) :
    (encodeV (p := p) w s)[i]'hi = (((s.toList[i]'h).toUInt8.toNat : ℕ) : ZMod p) := by
  simp [encodeV, h]

/-- Every entry of the encoding is a byte: a character's low byte, or the padding `0`. -/
lemma encodeV_val_lt {w : ℕ} {s : String} {i : ℕ} (hi : i < w) :
    ((encodeV (p := p) w s)[i]'hi).val < 256 := by
  by_cases h : i < s.toList.length
  · rw [encodeV_getElem_of_lt hi h, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (UInt8.toNat_lt_size _)
  · simp [encodeV, h]

abbrev conversion {w} : Conversion p (FString p w) where
  IdealT := String
  toExprs x := x.data.toList ++ [x.len]
  conversion s := (encodeV w s).toList ++ [(s.length : ZMod p)]

lemma converts_intro
  {w}
  {state : ClapMState p}
  {fs : FString p w}
  {s : String}
  (h_data : Converts FVec.conversion state fs.data (encodeV w s))
  (h_len : Converts F.conversion state fs.len (s.length : ZMod p))
:
  Converts conversion state fs s
:= by
  have h_len_data : fs.data.toList.length = w := by simp
  have h_len_enc : (encodeV (p := p) w s).toList.length = w := by simp
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro ⟨i, h_i⟩
    simp only [conversion, Fin.getElem_fin] at h_i ⊢
    by_cases h : i < w
    · rw [List.getElem_append_left (by omega)]
      simpa using h_data.varSet_wf ⟨i, by simpa using h⟩
    · have hi : i = w := by simp at h_i; omega
      subst hi
      rw [List.getElem_append_right (by omega)]
      simp only [h_len_data, Nat.sub_self]
      simpa using h_len.varSet_wf ⟨0, by simp⟩
  · intro ⟨i, h_i⟩
    simp only [conversion, Fin.getElem_fin] at h_i ⊢
    by_cases h : i < w
    · rw [List.getElem_append_left (by omega)]
      simpa using h_data.expr_wf ⟨i, by simpa using h⟩
    · have hi : i = w := by simp at h_i; omega
      subst hi
      rw [List.getElem_append_right (by omega)]
      simp only [h_len_data, Nat.sub_self]
      simpa using h_len.expr_wf ⟨0, by simp⟩
  · intro ⟨i, h_i⟩
    simp only [conversion, Fin.getElem_fin] at h_i ⊢
    by_cases h : i < w
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
      simpa using h_data.value_eq ⟨i, by simpa using h⟩
    · have hi : i = w := by simp at h_i; omega
      subst hi
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp only [h_len_data, h_len_enc, Nat.sub_self]
      simpa using h_len.value_eq ⟨0, by simp⟩

lemma converts_data
  {w}
  {state : ClapMState p}
  {fs : FString p w}
  {s : String}
  (h : Converts conversion state fs s)
:
  Converts FVec.conversion state fs.data (encodeV w s)
:= by
  have h_len_data : fs.data.toList.length = w := by simp
  have h_len_enc : (encodeV (p := p) w s).toList.length = w := by simp
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro ⟨i, h_i⟩
    have hw : i < w := by simpa using h_i
    have := h.varSet_wf ⟨i, by simp; omega⟩
    simp only [conversion, Fin.getElem_fin] at this
    rwa [List.getElem_append_left (by omega)] at this
  · intro ⟨i, h_i⟩
    have hw : i < w := by simpa using h_i
    have := h.expr_wf ⟨i, by simp; omega⟩
    simp only [conversion, Fin.getElem_fin] at this
    rwa [List.getElem_append_left (by omega)] at this
  · intro ⟨i, h_i⟩
    have hw : i < w := by simpa using h_i
    have := h.value_eq ⟨i, by simp; omega⟩
    simp only [conversion, Fin.getElem_fin] at this
    rwa [List.getElem_append_left (by omega),
         List.getElem_append_left (by omega)] at this

lemma converts_len
  {w}
  {state : ClapMState p}
  {fs : FString p w}
  {s : String}
  (h : Converts conversion state fs s)
:
  Converts F.conversion state fs.len (s.length : ZMod p)
:= by
  have h_len_data : fs.data.toList.length = w := by simp
  have h_len_enc : (encodeV (p := p) w s).toList.length = w := by simp
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro ⟨i, h_i⟩
    have hi : i = 0 := by simpa using h_i
    subst hi
    have := h.varSet_wf ⟨w, by simp⟩
    simp only [conversion, Fin.getElem_fin] at this
    rw [List.getElem_append_right (by omega)] at this
    simpa [h_len_data] using this
  · intro ⟨i, h_i⟩
    have hi : i = 0 := by simpa using h_i
    subst hi
    have := h.expr_wf ⟨w, by simp⟩
    simp only [conversion, Fin.getElem_fin] at this
    rw [List.getElem_append_right (by omega)] at this
    simpa [h_len_data] using this
  · intro ⟨i, h_i⟩
    have hi : i = 0 := by simpa using h_i
    subst hi
    have := h.value_eq ⟨w, by simp⟩
    simp only [conversion, Fin.getElem_fin] at this
    rw [List.getElem_append_right (by omega),
        List.getElem_append_right (by omega)] at this
    simpa [h_len_data, h_len_enc] using this

end FString

end Clap.Lang
