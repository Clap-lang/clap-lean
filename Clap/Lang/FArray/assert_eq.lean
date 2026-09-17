import Clap.Lang.Combinators.foldlM
import Clap.Lang.FUnit.assert_eq

namespace Clap.Lang.FArray

variable {p : ℕ}

section assert_eq

/-- Assert two bit vectors are equal, position by position. -/
def assert_eq {w : ℕ} (a b : FArray p w) : ClapM p Unit :=
  (a.zip b).foldlM (fun _ xy ↦ _root_.Clap.Lang.assert_eq xy.1 xy.2) ()

namespace assert_eq

private lemma step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc : Unit}
  {acc_val : Unit}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (_h_acc : Converts FUnit.conversion state acc acc_val)
  (h_xy : Converts FPair.conversion state xy xy_val)
:
  ConvertsM FUnit.conversion (_root_.Clap.Lang.assert_eq xy.1 xy.2) state ()
    (xy_val.1 = xy_val.2)
:= _root_.Clap.Lang.assert_eq.convertsM (FPair.converts_fst h_xy) (FPair.converts_snd h_xy)

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a b : FArray p w}
  {a_vals b_vals : Vector Bool w}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
:
  ConvertsM FUnit.conversion (assert_eq a b) state ()
    (∀ i : Fin w, a_vals[i] = b_vals[i])
:= by
  haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
  unfold assert_eq

  have h_a_f := FVec.converts_of_FArray_converts h_a
  have h_b_f := FVec.converts_of_FArray_converts h_b

  have h_elems : ∀ i : Fin w,
      Converts FPair.conversion state (a.zip b)[i]
        (((a_vals.map (fun x ↦ if x then (1 : ZMod p) else 0)).zip
          (b_vals.map (fun x ↦ if x then (1 : ZMod p) else 0)))[i]) :=
    fun i ↦ FVec.converts_zip h_a_f h_b_f i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints
      (f_spec := fun (_ : Unit) (_ : ZMod p × ZMod p) ↦ ())
      (step_constraints := fun (xy : ZMod p × ZMod p) ↦ xy.1 = xy.2)
      (init_val := ())
      h_elems FUnit.converts step_convertsM)
  . rfl
  . constructor
    . intro h ⟨i, h_i⟩
      have := h ⟨i, h_i⟩
      simp at this
      by_cases hb : b_vals[i] <;> by_cases ha : a_vals[i] <;>
        simp [ha, hb] at this ⊢
    . intro h ⟨i, h_i⟩
      have := h ⟨i, h_i⟩
      simp
      grind

end assert_eq
end assert_eq

end Clap.Lang.FArray
