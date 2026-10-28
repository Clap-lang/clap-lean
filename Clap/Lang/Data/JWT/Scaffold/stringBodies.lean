import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.xorScan
import Batteries.Data.String.Lemmas
import Batteries.Data.ByteArray

namespace Clap.Lang

variable {p : ℕ}

namespace stringBodies

/-! ### Bridging `String.toAsciiByteArray` to `String.toList`

`toAsciiByteArray` is defined by its own hand-rolled position loop
(`.lake/packages/batteries/Batteries/Data/String/Basic.lean`), with no library lemmas relating it
to `toList`. These three lemmas establish that bridge: `toAsciiByteArray` pushes exactly one byte
(`c.toUInt8`) per character of `toList`, in order. -/

open String in
private theorem toAsciiByteArray_loop_append (s : String) :
    ∀ (p : Pos.Raw) (out : ByteArray),
      String.toAsciiByteArray.loop s p out = out ++ String.toAsciiByteArray.loop s p ByteArray.empty := by
  intro p
  induction hm : (s.utf8ByteSize - p.byteIdx) using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    intro out
    by_cases h : p.atEnd s
    · simp [String.toAsciiByteArray.loop, h]
    · rw [String.toAsciiByteArray.loop, String.toAsciiByteArray.loop, dif_neg h, dif_neg h]
      have hlt : s.utf8ByteSize - (Pos.Raw.next s p).byteIdx < s.utf8ByteSize - p.byteIdx :=
        Nat.sub_lt_sub_left (Nat.lt_of_not_le <| mt decide_eq_true h)
          (Nat.lt_add_of_pos_right (Char.utf8Size_pos _))
      have key := ih (s.utf8ByteSize - (Pos.Raw.next s p).byteIdx) (by omega) (Pos.Raw.next s p) rfl
      have happend_push : ∀ (a b : ByteArray) (c : UInt8), a ++ b.push c = (a ++ b).push c := by
        intro a b c; apply ByteArray.ext; simp
      rw [key (out.push (p.get s).toUInt8), key (ByteArray.empty.push (p.get s).toUInt8),
          ← ByteArray.append_assoc, happend_push, ByteArray.append_empty]

open String in
private theorem toAsciiByteArray_loop_of_valid (cs' : List Char) :
    ∀ (cs : List Char) (out : ByteArray),
      String.toAsciiByteArray.loop (String.ofList (cs ++ cs')) ⟨utf8Len cs⟩ out
        = out ++ ⟨(cs'.map Char.toUInt8).toArray⟩ := by
  induction cs' with
  | nil =>
    intro cs out
    rw [String.toAsciiByteArray.loop, dif_pos (by rw [String.atEnd_of_valid])]
    apply ByteArray.ext
    simp
  | cons c cs'' ih =>
    intro cs out
    have hnot : ¬ Pos.Raw.atEnd (String.ofList (cs ++ c :: cs'')) (⟨utf8Len cs⟩ : Pos.Raw) := by
      rw [String.atEnd_of_valid]; simp
    have step1 : String.toAsciiByteArray.loop (String.ofList (cs ++ c :: cs'')) ⟨utf8Len cs⟩ out
        = String.toAsciiByteArray.loop (String.ofList (cs ++ c :: cs''))
            (Pos.Raw.next (String.ofList (cs ++ c :: cs'')) ⟨utf8Len cs⟩)
            (out.push ((⟨utf8Len cs⟩ : Pos.Raw).get (String.ofList (cs ++ c :: cs''))).toUInt8) := by
      rw [String.toAsciiByteArray.loop, dif_neg hnot]
    have hget : (⟨utf8Len cs⟩ : Pos.Raw).get (String.ofList (cs ++ c :: cs'')) = c :=
      String.get_of_valid cs (c :: cs'')
    have hnext : Pos.Raw.next (String.ofList (cs ++ c :: cs'')) ⟨utf8Len cs⟩ = ⟨utf8Len (cs ++ [c])⟩ := by
      rw [String.next_of_valid cs c cs'']
      congr 1
      simp [utf8Len]
    rw [hget, hnext] at step1
    have step2 := ih (cs ++ [c]) (out.push c.toUInt8)
    rw [show cs ++ [c] ++ cs'' = cs ++ c :: cs'' from by simp] at step2
    rw [step2] at step1
    rw [step1]
    apply ByteArray.ext
    simp

private theorem toAsciiByteArray_eq (s : String) :
    s.toAsciiByteArray = ⟨(s.toList.map Char.toUInt8).toArray⟩ := by
  have hs : s = String.ofList s.toList := (String.ofList_toList (s := s)).symm
  rw [String.toAsciiByteArray]
  have h := toAsciiByteArray_loop_of_valid s.toList [] ByteArray.empty
  simp only [List.nil_append, String.utf8Len] at h
  conv_lhs => rw [hs]
  exact h.trans (by apply ByteArray.ext; simp)

theorem toAsciiByteArray_size (s : String) : s.toAsciiByteArray.size = s.toList.length := by
  rw [toAsciiByteArray_eq]
  simp [ByteArray.size]

theorem toAsciiByteArray_getElem (s : String) (i : ℕ) (h : i < s.toAsciiByteArray.size) :
    s.toAsciiByteArray[i] = (s.toList[i]'(by rwa [toAsciiByteArray_size] at h)).toUInt8 := by
  have heq := toAsciiByteArray_eq s
  have hi : i < s.toList.length := by rwa [toAsciiByteArray_size] at h
  simp only [ByteArray.getElem_eq_data_getElem] at *
  simp only [heq]
  simp [List.getElem_map]

lemma getElem_scanl_succ {k} (f : ZMod p → ZMod p → ZMod p) (init : ZMod p)
    (vals : Vector (ZMod p) k) (i : ℕ) (hi1 : i + 1 < k) :
    (Vector.scanl f init vals)[i+1]'hi1 = f ((Vector.scanl f init vals)[i]'(by omega)) (vals[i]'(by omega)) := by
  rw [Vector.getElem_scanl, Vector.getElem_scanl]
  rw [List.take_succ_eq_append_getElem (by simp; omega), List.foldl_append]
  simp [Vector.getElem_toList]

private lemma uint8_eq_iff_cast_eq (h_p : 256 < p) (u v : UInt8) :
    (u = v) ↔ ((u.toNat : ZMod p) = (v.toNat : ZMod p)) := by
  have hsize : UInt8.size = 256 := rfl
  have hu := u.toNat_lt_size
  have hv := v.toNat_lt_size
  rw [hsize] at hu hv
  constructor
  · intro h; rw [h]
  · intro h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    exact UInt8.toNat_inj.mp hval

lemma quoteByte_eq (h_p : 256 < p) (u : UInt8) :
    decide (u = '"'.toUInt8) = ((u.toNat : ZMod p) == (34 : ZMod p)) := by
  rw [Bool.beq_eq_decide_eq, decide_eq_decide]
  rw [uint8_eq_iff_cast_eq h_p]
  norm_num [show ('"'.toUInt8.toNat : ℕ) = 34 from by decide]

lemma backslashByte_eq (h_p : 256 < p) (u : UInt8) :
    decide (u = '\\'.toUInt8) = ((u.toNat : ZMod p) == (92 : ZMod p)) := by
  rw [Bool.beq_eq_decide_eq, decide_eq_decide]
  rw [uint8_eq_iff_cast_eq h_p]
  norm_num [show ('\\'.toUInt8.toNat : ℕ) = 92 from by decide]

set_option linter.unnecessarySeqFocus false in
lemma mul_one_sub_ite (a b : Bool) :
    (if a then (1:ZMod p) else 0) * (1 - (if b then (1:ZMod p) else 0))
      = (if (a && !b) then (1:ZMod p) else 0) := by
  cases a <;> cases b <;> simp

set_option linter.unnecessarySeqFocus false in
lemma add_sub_two_mul_ite (a b : Bool) :
    (if a then (1:ZMod p) else 0) + (if b then (1:ZMod p) else 0)
      - 2 * (if a then (1:ZMod p) else 0) * (if b then (1:ZMod p) else 0)
      = (if xor a b then (1:ZMod p) else 0) := by
  cases a <;> cases b <;> simp <;> ring

/-- Unconditional version of `Clap.Lang.scanAux.convertsM`'s closed form specialized to a
one-hot input (the shape `oneHotRaw`'s ideal value has): the entry-`m` value of the running XOR
scan is `init_val ^^ decide (a < m)`, with no hypothesis relating `a` to `len`. Copied from the
private lemma of the same name in `leftArraySelector.lean` — that file's version carries no
such hypothesis either, since the range check there comes entirely from `singleOneArray`, not
from this computation. -/
lemma scanAuxPure_getElem_uncond
  {len a : ℕ} {init_val : Bool}
  (j : ℕ) (hj : j ≤ len) (m : ℕ) (hm : m ≤ j)
:
  (scanAuxPure (Vector.ofFn (fun t : Fin len => t.val == a)) init_val j hj)[m]'(by omega)
    = (init_val ^^ decide (a < m))
:= by
  induction j generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    unfold scanAuxPure
    simp
  | succ j ih =>
    unfold scanAuxPure
    by_cases hmj : m ≤ j
    . rw [Vector.getElem_push_lt]
      exact ih (by omega) m hmj
    . have hmj' : m = j + 1 := by omega
      subst hmj'
      rw [Vector.getElem_push_eq]
      have h_rest_j := ih (by omega) j (le_refl j)
      have hlt : (a < j + 1) ↔ (a < j ∨ a = j) := by omega
      simp only [h_rest_j, hlt, Bool.decide_or]
      cases init_val <;>
        by_cases ha : a < j <;> by_cases ha2 : a = j <;>
        simp [ha, ha2] <;> omega

end stringBodies

end Clap.Lang
