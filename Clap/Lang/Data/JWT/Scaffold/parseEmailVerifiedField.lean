import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.eq0
import Clap.Util.Wheels
import Clap.Model.Convert.PaddedVector
import Clap.Util.Primes
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Clap.Lang.Data.JWT.Basic
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

/-- `field_vals.getD idx 0` is always a byte: in range it is `field_vals[idx]`, out of range it
is the default `0`. -/
lemma getD_byte_bound {k : ℕ} {field_vals : Vector (ZMod bn254) k}
    (h_byte : ∀ i : Fin k, field_vals[i].val < 2 ^ 8) (idx : ℕ) :
    (field_vals.getD idx 0).val < 2 ^ 8 := by
  by_cases h : idx < k
  · have := h_byte ⟨idx, h⟩
    simpa [Vector.getD, h] using this
  · simp [Vector.getD, h]

/-- `F8.isWhitespace`'s checked value (`UInt8` comparisons against a byte known `< 2^8`) equals
the plain-`ℕ` `isWs` predicate used throughout this file's specs. -/
private lemma isWhitespace_val_eq {c_val : ZMod bn254} (h_c8 : c_val.val < 2 ^ 8) :
    ((UInt8.ofNat c_val.val) > 8 && (UInt8.ofNat c_val.val) < 14 || (UInt8.ofNat c_val.val) = 32)
      = isWs c_val.val := by
  have h32 : (UInt8.toNat 32) = 32 := by decide
  have h8 : (UInt8.toNat 8) = 8 := by decide
  have h14 : (UInt8.toNat 14) = 14 := by decide
  simp only [isWs, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_ofNat',
    h32, h8, h14, Nat.mod_eq_of_lt h_c8]

/-- `F8.isWhitespace`'s *unchecked* raw value (in terms of `lessThan.lessThanRaw`, for a byte
consumed without a typed `F8.conversion` fact) equals the plain-`ℕ` `isWs` predicate, given the
byte is known `< 2^8`. Companion to `isWhitespace_val_eq` above, which does the same for the
*checked*, `UInt8`-typed form; `checkWhitespaceZones`'s per-element `foldlM` step can only use the
unchecked form (its combinator has no way to thread a per-index range hypothesis), hence needs
this version instead. -/
lemma lessThanRaw_isWs_eq {c_val : ZMod bn254} (h_c8 : c_val.val < 2 ^ 8) :
    ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32)
      = isWs c_val.val := by
  have hw9 : (2:ℕ) ^ (8 + 1) < bn254 := by decide
  have h8v : (8 : ZMod bn254).val = 8 := by decide
  have h14v : (14 : ZMod bn254).val = 14 := by decide
  have h8lt : (8 : ZMod bn254).val < 2 ^ 8 := by decide
  have h14lt : (14 : ZMod bn254).val < 2 ^ 8 := by decide
  have h32eq : (c_val == (32 : ZMod bn254)) = decide (c_val.val = 32) := by
    have h32v : (32 : ZMod bn254).val = 32 := by decide
    by_cases h : c_val.val = 32
    · have hc : c_val = 32 := ZMod.val_injective bn254 (by rw [h32v]; exact h)
      simp [hc, h32v]
    · have hne : c_val ≠ 32 := fun hc => h (by rw [hc, h32v])
      simp [hne, h]
  rw [lessThan.lessThanRaw_eq h8lt h_c8 hw9, lessThan.lessThanRaw_eq h_c8 h14lt hw9, h32eq, h8v, h14v]
  simp [isWs]

/-! ## `Vector.zipWithM`: a combinator lemma with nowhere layering-safe to live

`Vector.zipWithM` (`Clap/Lang/Poseidon/Poseidon.lean`) is generic, model-agnostic Vector plumbing
that happens to be defined in a Poseidon file. `Lang/Core/Combinators/` (where the other
`convertsM_*` combinator lemmas live) sits *below* `Lang/Poseidon` in the import order
(`Gate → Core → Poseidon → Data`), so a lemma about it cannot live there without a layering
violation. `Lang/Data/JWT` sits above `Lang/Poseidon`, so it is kept here, private to this file's
only two current uses (`checkWhitespaceZones` below, and `parseJWTFieldWithUnquotedValue`'s
identical zone merge later). -/

private lemma Vector.zipWithM_zero {m} [Monad m] [LawfulMonad m] {α β φ : Type}
    (f : α → β → m φ) :
  Vector.zipWithM f (#v[] : Vector α 0) (#v[] : Vector β 0) = pure #v[]
:= by
  unfold Vector.zipWithM
  simp

private lemma Vector.zipWithM_succ {m} [Monad m] {n} {α β φ : Type}
    (f : α → β → m φ) (a : α) (b : β) (xs : Vector α n) (ys : Vector β n) :
  Vector.zipWithM f (⟨⟨a :: xs.toList⟩, by simp⟩ : Vector α (n+1))
                    (⟨⟨b :: ys.toList⟩, by simp⟩ : Vector β (n+1))
  = (do
      let z ← f a b
      let zs ← xs.zipWithM f ys
      pure (⟨⟨z :: zs.toList⟩, by simp⟩ : Vector φ (n+1)))
:= by
  conv_lhs => unfold Vector.zipWithM
  simp [Vector.head, List.take_of_length_le Vector.length_toList.le, Vector.toArray_toList]

private lemma FArray.converts_cons
  {p : ℕ} {k} {state : ClapMState p}
  {expr : FB p} {val : Bool}
  {exprs : FArray p k} {vals : Vector Bool k}
  (h_expr : Converts FB.conversion state expr val)
  (h_exprs : Converts FArray.conversion state exprs vals)
:
  Converts FArray.conversion state (⟨⟨expr :: exprs.toList⟩, by simp⟩ : Vector (FB p) (k + 1))
    (⟨⟨val :: vals.toList⟩, by simp⟩ : Vector Bool (k + 1))
:= by
  rewrite [FArray.converts_iff_FB_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  match i, h_i with
  | 0, h_i => simpa using h_expr
  | i + 1, h_i =>
    have h := h_exprs ⟨i, by omega⟩
    simpa using h

/-- The `foldlM` step: whitespace-or-not for one position, given its `and`-selector bit `z` and
field character `c` as *general* field elements (not necessarily typed bits/bytes) — the
combinator's per-element hypothesis has no room to carry a per-index byte-range fact, so this uses
`F8.isWhitespace`'s *unchecked* form and `FB.and`'s underlying `mkMul` directly, matching how
`checkCharBeforeValue`'s tail handles its own "not actually known to be a bit" product. -/
lemma whitespaceCheck_convertsM
  {state : ClapMState bn254} {z c : F bn254} {z_val c_val : ZMod bn254}
  (h_z : Converts F.conversion state z z_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM FUnit.conversion
    (F8.isWhitespace c >>= fun ws => not ws >>= fun notws => FB.and z notws >>= fun prod => eq0 prod)
    state ()
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      z_val * (if ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) ||
        c_val == 32) then (0:ZMod bn254) else 1) = 0 )
:= by
  have hWs := F8.isWhitespace.convertsM_unchecked h_c
  replace h_z := converts_skip hWs h_z
  apply convertsM_bind_and hWs
  refine convertsM_bind (not.convertsM hWs.result) ?_ (fun _ => trivial)
  have hNot := not.convertsM hWs.result
  replace h_z := converts_skip hNot h_z
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)) ?_ (fun _ => trivial)
  apply convertsM_of_convertsM
    (eq0.convertsM (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)).result)
  · rfl
  · by_cases h : (lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32 <;>
      simp [h]

/-- `Vector.zipWithM FB.or`: a `True`-constraint, pointwise-OR combinator. Covers both zone
merges in `checkWhitespaceZones` below. -/
lemma convertsM_zipWithM_or
  {p : ℕ} [p.AtLeastTwo]
  {k} {state : ClapMState p}
  {xs ys : Vector (FB p) k} {xvals yvals : Vector Bool k}
  (h_x : ∀ i : Fin k, Converts FB.conversion state xs[i] xvals[i])
  (h_y : ∀ i : Fin k, Converts FB.conversion state ys[i] yvals[i])
:
  ConvertsM FArray.conversion (xs.zipWithM FB.or ys) state
    (Vector.ofFn (fun i : Fin k => xvals[i] || yvals[i])) True
:= by
  induction k generalizing state with
  | zero =>
    have hxs : xs = #v[] := by grind
    have hys : ys = #v[] := by grind
    subst hxs hys
    rw [Vector.zipWithM_zero]
    apply convertsM_pure
    . have h_eq : (Vector.ofFn (fun i : Fin 0 => xvals[i] || yvals[i]) : Vector Bool 0) = #v[] := by
        ext i hi; omega
      rw [h_eq]
      exact FArray.converts_empty
    . trivial
  | succ k ih =>
    have h_head_x : Converts FB.conversion state xs[0] xvals[0] := h_x ⟨0, by omega⟩
    have h_head_y : Converts FB.conversion state ys[0] yvals[0] := h_y ⟨0, by omega⟩
    have h_tail_x : ∀ i : Fin k, Converts FB.conversion state
        (xs.tail.cast (by omega) : Vector (FB p) k)[i] (xvals.tail.cast (by omega) : Vector Bool k)[i] := by
      intro ⟨i, h_i⟩
      have h1 : (xs.tail.cast (by omega) : Vector (FB p) k)[i]'(by omega)
          = xs[i+1]'(by omega) := by simp [Nat.add_comm]
      have h2 : (xvals.tail.cast (by omega) : Vector Bool k)[i]'(by omega)
          = xvals[i+1]'(by omega) := by simp [Nat.add_comm]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_x ⟨i+1, by omega⟩
    have h_tail_y : ∀ i : Fin k, Converts FB.conversion state
        (ys.tail.cast (by omega) : Vector (FB p) k)[i] (yvals.tail.cast (by omega) : Vector Bool k)[i] := by
      intro ⟨i, h_i⟩
      have h1 : (ys.tail.cast (by omega) : Vector (FB p) k)[i]'(by omega)
          = ys[i+1]'(by omega) := by simp [Nat.add_comm]
      have h2 : (yvals.tail.cast (by omega) : Vector Bool k)[i]'(by omega)
          = yvals[i+1]'(by omega) := by simp [Nat.add_comm]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_y ⟨i+1, by omega⟩
    rw [Vector.eq_cons xs, Vector.eq_cons ys, Vector.zipWithM_succ]
    have h_action := FB.or.convertsM h_head_x h_head_y
    have h_tail_x' := fun i ↦ converts_skip h_action (h_tail_x i)
    have h_tail_y' := fun i ↦ converts_skip h_action (h_tail_y i)
    step h_action as z
    step (ih h_tail_x' h_tail_y') as zs
    apply convertsM_pure
    . have h_cons := FArray.converts_cons h_z h_zs
      have h_vals : Vector.ofFn (fun i : Fin (k+1) => xvals[i] || yvals[i])
          = (⟨⟨(xvals[0] || yvals[0]) :: (Vector.ofFn (fun i : Fin k =>
              (xvals.tail.cast (by omega) : Vector Bool k)[i] ||
              (yvals.tail.cast (by omega) : Vector Bool k)[i])).toList⟩, by simp⟩
             : Vector Bool (k+1)) := by
        ext i hi
        rcases i with _ | i
        · simp
        · simp [Nat.add_comm]
      rw [h_vals]
      simpa using h_cons
    . trivial

namespace parseEmailVerifiedField

open Poseidon RandomOracle Primes FiatShamir

open FString

/-- Reads a character's byte out of `(encodeV w S).getD i 0`, when `i` is in bounds for both `w`
and `S` — the `getD` counterpart of `encodeV_getElem_of_lt`, needed because `complete` below
reasons about specific literal offsets in `field` via `Vector.getD`/`List.getD`. Mirrors
`parseJWTFieldSharedLogic.encodeV_getD_of_lt`, which is `private` to that file and so not visible
here. -/
lemma encodeV_getD_of_lt {w i : ℕ} {S : String} (hw : i < w) (hs : i < S.toList.length) :
    (encodeV (p := bn254) w S).getD i 0 =
      (((S.toList.getD i default).toUInt8.toNat : ℕ) : ZMod bn254) := by
  rw [show (encodeV (p := bn254) w S).getD i 0 = (encodeV (p := bn254) w S)[i]'hw from by
    simp [Vector.getD, hw]]
  rw [encodeV_getElem_of_lt hw hs, show S.toList[i]'hs = S.toList.getD i default from by
    simp [List.getD_eq_getElem?_getD, hs]]

/-- `(encodeV w S).getD i 0` is `0` once `i` is past the end of `S`, whether or not it is still
within `w`: `encodeV`'s own `if` falls to its `else` branch, and `Vector.getD` past `w` is its
default. Companion to `encodeV_getD_of_lt`, needed for `complete`'s quote-match argument when the
character before/after the value sits in `field`'s zero-padding. -/
lemma encodeV_getD_of_ge {w i : ℕ} {S : String} (h : S.toList.length ≤ i) :
    (encodeV (p := bn254) w S).getD i 0 = 0 := by
  by_cases hw : i < w
  · rw [show (encodeV (p := bn254) w S).getD i 0 = (encodeV (p := bn254) w S)[i]'hw from by
      simp [Vector.getD, hw]]
    simp [encodeV, Nat.not_lt.mpr h]
  · simp [Vector.getD, hw]

end parseEmailVerifiedField

end Clap.Lang
