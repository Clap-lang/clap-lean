import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Data.FArray.singleOneArray
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.FB.or

namespace Clap.Lang

variable {p : ℕ}

/-- Outputs a bit array with 1s at `(idx, len)` and 0s at `[0, idx]`. Only satisfiable when
`0 ≤ idx < len`. -/
def rightArraySelector [p.AtLeastTwo] (len : ℕ) (idx : F p) :
  ClapM p (FArray p len)
:= do
  let bits : FArray p len ← singleOneArray len idx
  let false' ← FB.ofBool false
  bits.scanlM FB.or false'

namespace rightArraySelector

private lemma ofFn_succ' {α} {len} (f : Fin (len + 1) → α) :
  (Vector.ofFn f : Vector α (len + 1)) =
    (⟨⟨f 0 :: (Vector.ofFn (fun i : Fin len => f i.succ)).toList⟩, by simp⟩ : Vector α (len + 1))
:= by
  apply Vector.toList_inj.mp
  simp [Vector.toList_ofFn, List.ofFn_succ]

/-- Closed form for an exclusive-prefix-OR scan of a one-hot (or all-zero) vector: position `m`
is `init_val` OR'd with whether the one-hot bit at `start + j` (for some `j < m`) was set. -/
private lemma scanl_oneHot_getElem
  {start len a : ℕ} {init_val : Bool} (m : ℕ) (hm : m < len) :
  (Vector.scanl (· || ·) init_val
      (Vector.ofFn (fun t : Fin len => (start + t.val) == a)))[m]'(by omega) =
    (init_val || decide (start ≤ a ∧ a < start + m))
:= by
  induction len generalizing start init_val m with
  | zero => omega
  | succ len ih =>
    rw [ofFn_succ']
    rw [Vector.scanl_succ]
    match m, hm with
    | 0, hm => simp
    | m + 1, hm =>
      simp
      have h := ih (start := start + 1) (init_val := init_val || (start == a)) m (by omega)
      rw [show (fun i : Fin len => (start + 1) + i.val == a) =
            (fun i : Fin len => start + (i.val + 1) == a) from by
        funext i; congr 1; omega] at h
      rw [h]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
      cases init_val <;> simp <;> omega

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F p}
  {state : ClapMState p}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (rightArraySelector len idx) state
    (Vector.ofFn (fun i : Fin len => idx_val.val < i.val))
    (idx_val.val < len)
:= by
  unfold rightArraySelector
  step singleOneArray.convertsM h_idx h_len as bits
  step (FB.ofBool.convertsM (state := bits_state) (b := false)) as false'
  apply convertsM_of_convertsM (Vector.scanlM.convertsM h_bits h_false')
  . ext i hi
    simp only [Vector.getElem_ofFn]
    have h := scanl_oneHot_getElem (start := 0) (a := idx_val.val) (init_val := false) i (by omega)
    simp only [Nat.zero_add] at h
    rw [h]
    simp
  . simp

end rightArraySelector

end Clap.Lang
