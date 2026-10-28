import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.Combinators.foldlM
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Clap.Lang.Data.JWT.Basic
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

/-! ## Generic logic helpers

A fixed guard (`perform`) commutes with a position-indexed `∀`: the guard does not depend on the
index, so "for every position, if guarded then P" is the same as "if guarded then for every
position, P". Used to pull `perform_val = true →` outside the `∀ i` produced by the `foldlM`
combinators below. -/

lemma forall_guard_comm {ι : Type} {g : Prop} {B : ι → Prop} :
    (∀ i, g → B i) ↔ (g → ∀ i, B i) :=
  ⟨fun h hg i => h i hg, fun h i hg => h hg i⟩

lemma forall_and_guard_comm {ι : Type} {A : ι → Prop} {g : Prop} {B : ι → Prop} :
    (∀ i, A i ∧ (g → B i)) ↔ (∀ i, A i) ∧ (g → ∀ i, B i) :=
  ⟨fun h => ⟨fun i => (h i).1, fun hg i => (h i).2 hg⟩,
   fun h i => ⟨h.1 i, fun hg => h.2 hg i⟩⟩

/-- `convertsM_foldlM_constraints` (`Clap/Lang/Core/Combinators/foldlM.lean`) for a step that also
reads a fixed context `ctx` — here, the guard `perform`, allocated once before each loop in this
file and threaded through every iteration's guarded assertion. No existing combinator covers both
context-threading (`convertsM_foldlM_ctx`) and a real per-step constraint
(`convertsM_foldlM_constraints`) at once; this merges the two inductions. -/
lemma convertsM_foldlM_ctx_constraints
  {p : ℕ} {k} {α γ δ}
  {C_ctx : Conversion p δ}
  {C_acc : Conversion p α}
  {C_elem : Conversion p γ}
  {f : δ → α → γ → ClapM p α}
  {f_spec : C_ctx.IdealT → C_acc.IdealT → C_elem.IdealT → C_acc.IdealT}
  {step_constraints : C_ctx.IdealT → C_elem.IdealT → Prop}
  {state : ClapMState p}
  {ctx : δ}
  {ctx_val : C_ctx.IdealT}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  {init : α}
  {init_val : C_acc.IdealT}
  (h_ctx : Converts C_ctx state ctx ctx_val)
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_init : Converts C_acc state init init_val)
  (h_f : ∀ {state' : ClapMState p} {acc acc_val x x_val},
          Converts C_ctx state' ctx ctx_val →
          Converts C_acc state' acc acc_val →
          Converts C_elem state' x x_val →
          ConvertsM C_acc (f ctx acc x) state' (f_spec ctx_val acc_val x_val)
            (step_constraints ctx_val x_val))
:
  ConvertsM C_acc (v.foldlM (f ctx) init) state (vals.foldl (f_spec ctx_val) init_val)
    (∀ i : Fin k, step_constraints ctx_val vals[i])
:= by
  induction' k with k h_k
  . have h_empty : Vector.foldlM (m := ClapM p) (f ctx) init v = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := v
      grind
    simp [h_empty]
    apply convertsM_pure
    . have : vals = #v[] := by grind
      simp [this]
      assumption
    . trivial
  . set v_base := Vector.cast (m := k) (by trivial) v.pop with h_v_base_def
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop with h_vals_base_def

    have h_eq : ∀ (j : ℕ) (hj : j < k), vals_base[j]'hj = vals[j]'(by omega) := by
      intro j hj
      simp [vals_base]

    have h_v_base : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      simp only [Fin.getElem_fin]
      rw [h1, h_eq i h_i]
      exact h_v ⟨i, by omega⟩

    have h_vals : vals = vals_base.push vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [vals_base]
      . grind

    have h_push : v = v_base.push v[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [v_base]
      . grind

    have h_last := h_v ⟨k, Nat.lt_succ_self k⟩
    have h_ih := h_k h_v_base

    rewrite [h_push]
    simp only [Vector.foldlM_push]

    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih
        (h_f (converts_skip h_ih h_ctx) h_ih.result (converts_skip h_ih h_last)))
    . conv_rhs => rewrite [h_vals]
      simp
    . constructor
      . rintro ⟨h_prefix, h_elem⟩ ⟨i, h_i⟩
        by_cases h : i = k
        . subst h
          exact h_elem
        . have h_lt : i < k := by grind
          have h1 := h_prefix ⟨i, h_lt⟩
          simp only [Fin.getElem_fin] at h1
          rwa [h_eq i h_lt] at h1
      . intro h
        refine ⟨fun ⟨i, h_i⟩ ↦ ?_, h ⟨k, Nat.lt_succ_self k⟩⟩
        have h1 := h ⟨i, by grind⟩
        simp only [Fin.getElem_fin] at h1 ⊢
        rwa [← h_eq i h_i] at h1

/-- The `foldlM` step: whitespace-or-not for one position, given its zone-membership bit `z` and
field character `c` as *general* field elements (not necessarily typed bits/bytes) — the
combinator's per-element hypothesis has no room to carry a per-index byte-range fact, so this uses
`F8.isWhitespace`'s *unchecked* form and `FB.and`'s underlying `mkMul` directly. Guarded analogue
of `parseEmailVerifiedField.lean`'s `whitespaceCheck_convertsM`: the assertion only fires when
`perform` holds. -/
lemma guardedWhitespaceCheck_convertsM
  {state : ClapMState bn254} {perform z c : F bn254} {perform_val : Bool} {z_val c_val : ZMod bn254}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_z : Converts F.conversion state z z_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM FUnit.conversion
    (F8.isWhitespace c >>= fun ws => not ws >>= fun notws => FB.and z notws >>= fun prod =>
      guardedEq0 perform prod)
    state ()
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      (perform_val = true → z_val * (if ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) ||
        c_val == 32) then (0:ZMod bn254) else 1) = 0) )
:= by
  have hWs := F8.isWhitespace.convertsM_unchecked h_c
  replace h_z := converts_skip hWs h_z
  replace h_perform := converts_skip hWs h_perform
  apply convertsM_bind_and hWs
  refine convertsM_bind (not.convertsM hWs.result) ?_ (fun _ => trivial)
  have hNot := not.convertsM hWs.result
  replace h_z := converts_skip hNot h_z
  replace h_perform := converts_skip hNot h_perform
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)) ?_ (fun _ => trivial)
  have hMul := mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)
  replace h_perform := converts_skip hMul h_perform
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform hMul.result)
  · rfl
  · by_cases h : (lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32 <;>
      simp [h]

/-- `c == lit` reduces to a comparison of `.val`s, given `lit`'s `.val` — the bridge
`isForbidden_eq_false_iff` (`parseJWTFieldWithUnquotedValue.lean`) uses at each of its three
literals `,`, `}`, `"`. -/
lemma zmod_beq_eq_val_beq (c lit : ZMod bn254) (n : ℕ) (hlit : lit.val = n) :
    (c == lit) = (c.val == n) := by
  by_cases h : c.val = n
  · have hc : c = lit := ZMod.val_injective bn254 (by rw [hlit]; exact h)
    simp [hc, hlit]
  · have hne : c ≠ lit := fun hc => h (by rw [hc, hlit])
    simp [hne, h]

/-- The XOR of two `decide (· ≤ i)` boundary bits is exactly the indicator of the half-open
interval `[a, b)` — what `arraySelector`'s pointwise meaning reduces to once endpoints are ordered
(`a < b`). -/
lemma xor_le_iff_interval {a b i : ℕ} (hab : a < b) :
    (decide (a ≤ i) ^^ decide (b ≤ i)) = true ↔ a ≤ i ∧ i < b := by
  by_cases hai : a ≤ i <;> by_cases hib : b ≤ i <;> simp [hai, hib] <;> omega

end Clap.Lang
