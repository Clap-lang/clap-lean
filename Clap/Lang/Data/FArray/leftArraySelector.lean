import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Data.FArray.singleOneArray
import Clap.Lang.Data.FArray.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang

variable {p : ℕ}

/-- Outputs a bit array with 1s at `[0, idx)` and 0s at `[idx, len)`. Only satisfiable when
`0 ≤ idx < len`. -/
def leftArraySelector [p.AtLeastTwo] (len : ℕ) (idx : F p) :
  ClapM p (FArray p len)
:= do
  let bits : FArray p len ← singleOneArray len idx
  let true' ← FB.ofBool true
  bits.xorScan true'

namespace leftArraySelector

private lemma scanAuxPure_getElem
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

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F p}
  {state : ClapMState p}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (leftArraySelector len idx) state
    (Vector.ofFn (fun i : Fin len => decide (i.val < idx_val.val)))
    (idx_val.val < len)
:= by
  unfold leftArraySelector
  step singleOneArray.convertsM h_idx h_len as bits
  step (FB.ofBool.convertsM (state := bits_state) (b := true)) as true'
  apply convertsM_of_convertsM (FArray.xorScan.convertsM h_true' h_bits)
  . have htail :
        ∀ (j : ℕ) (hj : j < len),
          (scanAuxPure (Vector.ofFn (fun t : Fin len => t.val == idx_val.val)) true len (le_refl len)).tail[j]'(by omega)
            = (scanAuxPure (Vector.ofFn (fun t : Fin len => t.val == idx_val.val)) true len (le_refl len))[j + 1]'(by omega) := by
      intro j hj
      simp [Nat.add_comm]
    ext i hi
    simp only [Vector.getElem_cast, Vector.getElem_ofFn]
    rw [htail i hi]
    rw [scanAuxPure_getElem (len := len) (a := idx_val.val) len (le_refl len) (i + 1) (by omega)]
    by_cases h : idx_val.val < i + 1
    . have h' : ¬ (i < idx_val.val) := by omega
      simp [h, h']
    . have h' : i < idx_val.val := by omega
      simp [h, h']
  . simp

end leftArraySelector

section examples

/-! The old model's vectors (`old/Clap/Array.lean`), run end to end. -/

private abbrev q : ℕ := 47

local instance instFactPrimeLeftArraySelectorQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def runSat (c : ClapM q Unit) : Bool :=
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

private def checkBits {n} (g : ClapM q (FArray q n)) (e : Vector Bool n) : ClapM q Unit := do
  let r ← g
  let e' ← e.mapM FB.ofBool
  FArray.assert_eq r e'

private def lsel (len : ℕ) (i : ZMod q) (out : Vector Bool len) : Bool :=
  runSat (checkBits (do leftArraySelector len (← mkF i)) out)

example : lsel 4 0 #v[false, false, false, false] = true := by native_decide
example : lsel 4 1 #v[true, false, false, false] = true := by native_decide
example : lsel 4 2 #v[true, true, false, false] = true := by native_decide
example : lsel 4 3 #v[true, true, true, false] = true := by native_decide
example : lsel 4 2 #v[true, false, false, false] = false := by native_decide
example : lsel 4 4 #v[true, true, true, true] = false := by native_decide
example : lsel 4 4 #v[false, false, false, false] = false := by native_decide

end examples

end Clap.Lang
