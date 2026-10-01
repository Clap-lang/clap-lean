import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FArray.singleOneArray
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Data.FArray.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang

variable {p : ℕ}

section rightArraySelector

/-- Bit array with 0s at `[0, idx]` and 1s at `(idx, len)`, Circom's `RightArraySelector`: the
exclusive prefix sums `out[0] = 0`, `out[i] = out[i-1] + bits[i-1]` of the one-hot mask of `idx`,
as a `Vector.scanlM` (after Andrei Burdusa's PR #74, which scans with `FB.or`; the sum is Circom's
linear step). Only satisfiable when `idx < len`, which `singleOneArray` enforces. -/
def rightArraySelector [p.AtLeastTwo] (len : ℕ) (idx : F p) : ClapM p (FArray p len) := do
  let bits ← singleOneArray len idx
  let z ← mkF 0
  Vector.scanlM (fun (acc b : F p) ↦ acc + b) z bits

namespace rightArraySelector

/-- The exclusive prefix sums of a one-hot vector at `j`: `1` strictly after `j`, `0` up to it. -/
private lemma foldl_take_oneHot {len : ℕ} (j : ℕ) :
    ∀ i, i ≤ len →
      ((List.ofFn fun x : Fin len ↦ if x.val = j then (1 : ZMod p) else 0).take i).foldl (· + ·) 0
        = if j < i then 1 else 0
  | 0, _ => by simp
  | i + 1, h => by
    rw [List.take_add_one, List.foldl_append, foldl_take_oneHot j i (by omega)]
    rw [List.getElem?_ofFn]
    simp only [show i < len by omega, Option.toList]
    simp only [dite_true, List.foldl_cons, List.foldl_nil]
    by_cases h1 : j < i
    · have : i ≠ j := by omega
      simp [h1, this, show j < i + 1 by omega]
    · by_cases h2 : i = j
      · subst h2; simp
      · simp [h1, h2, show ¬ j < i + 1 by omega]

/-- A field-valued `ConvertsM` whose values are all `0`/`1` is a bit-vector one. -/
private lemma convertsM_FArray_of_FVec {k : ℕ} {action : ClapM p (FArray p k)}
    {state : ClapMState p} {vals : Vector Bool k} {c : Prop}
    (h : ConvertsM FVec.conversion action state
      (vals.map fun b ↦ if b then (1 : ZMod p) else 0) c) :
    ConvertsM FArray.conversion action state vals c :=
  ⟨converts_cast h.result rfl rfl, h.wellFormed, h.constraints⟩

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {state : ClapMState p}
  {idx : F p}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (rightArraySelector len idx) state
    (Vector.ofFn fun i : Fin len ↦ decide (idx_val.val < i.val)) (idx_val.val < len)
:= by
  unfold rightArraySelector
  step singleOneArray.convertsM h_idx h_len as bits
  step mkF.convertsM as z
  have h_bits_f := FVec.converts_of_FArray_converts h_bits
  have h_v := fun i : Fin len ↦ FVec.converts_getElem h_bits_f i.isLt
  have h_scan := convertsM_scanlM (f := fun (acc b : F p) ↦ acc + b) (f_spec := fun a b ↦ a + b)
    h_v h_z (fun h_acc h_x ↦ mkAdd.convertsM h_acc h_x)
  have h_val : Vector.scanl (fun a b ↦ a + b) 0
      ((Vector.ofFn fun x : Fin len ↦ x.val == idx_val.val).map
        fun b ↦ if b = true then (1 : ZMod p) else 0) =
      (Vector.ofFn fun i : Fin len ↦ decide (idx_val.val < i.val)).map
        fun b ↦ if b then (1 : ZMod p) else 0 := by
    ext i hi
    rw [Vector.getElem_scanl _ _ _ _ hi, Vector.getElem_map, Vector.getElem_ofFn,
      Vector.toList_map, Vector.toList_ofFn]
    have := foldl_take_oneHot (p := p) (len := len) idx_val.val i (by omega)
    simp only [List.map_ofFn] at this ⊢
    convert this using 3
    · congr 1
      funext x
      simp [Function.comp, beq_iff_eq]
    · by_cases h : idx_val.val < i <;> simp [h]
  apply convertsM_of_convertsM
    (convertsM_FArray_of_FVec (convertsM_of_convertsM h_scan h_val Iff.rfl))
  · rfl
  · simp

end rightArraySelector

end rightArraySelector

section examples

/-! Circom's `RightArraySelector` notes, which are also the old model's vectors
(`old/Clap/Array.lean`), run end to end. -/

private abbrev q : ℕ := 47

local instance instFactPrimeRightArraySelectorQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def runSat (c : ClapM q Unit) : Bool :=
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

private def checkBits {n} (g : ClapM q (FArray q n)) (e : Vector Bool n) : ClapM q Unit := do
  let r ← g
  let e' ← e.mapM FB.ofBool
  FArray.assert_eq r e'

private def rsel (len : ℕ) (i : ZMod q) (out : Vector Bool len) : Bool :=
  runSat (checkBits (do rightArraySelector len (← mkF i)) out)

example : rsel 4 0 #v[false, true, true, true] = true := by native_decide
example : rsel 4 1 #v[false, false, true, true] = true := by native_decide
example : rsel 4 2 #v[false, false, false, true] = true := by native_decide
example : rsel 4 3 #v[false, false, false, false] = true := by native_decide
example : rsel 4 1 #v[false, true, true, true] = false := by native_decide
example : rsel 4 4 #v[false, false, false, false] = false := by native_decide

end examples


end Clap.Lang
