import Clap.Lang.Combinators.foldlM
import Clap.Lang.FB.and
import Clap.Lang.FB.eq
import Clap.Lang.FB.ofBool

namespace Clap.Lang.FVec

variable {p : ℕ}

section eq

/-- Is one vector of field elements equal to another, as a circuit bit. This is the same circuit
as `FArray.eq`; only the conversion cited in the specification differs. -/
def eq [p.AtLeastTwo] {w : ℕ} (a b : FVec p w) : ClapM p (FB p) := do
  let acc0 ← FB.ofBool true
  (a.zip b).foldlM (fun acc xy ↦ do FB.and acc (←_root_.Clap.Lang.eq xy.1 xy.2)) acc0

namespace eq

private lemma foldl_and_all {α} (g : α → Bool) (l : List α) (acc : Bool) :
  l.foldl (fun a x ↦ a && g x) acc = (acc && l.all g)
:= by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih => simp [ih, Bool.and_assoc]

private lemma zip_all_eq_decide :
  ∀ {l1 l2 : List (ZMod p)}, l1.length = l2.length →
    (l1.zip l2).all (fun xy ↦ xy.1 == xy.2) = decide (l1 = l2)
:= by
  intro l1
  induction l1 with
  | nil => intro l2 h; cases l2 <;> simp_all
  | cons x xs ih =>
    intro l2 h
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.all_cons]
      rw [ih (by simpa using h)]
      by_cases hxy : x = y <;> simp [hxy]

private lemma step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc : FB p}
  {acc_val : Bool}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (h_acc : Converts FB.conversion state acc acc_val)
  (h_xy : Converts FPair.conversion state xy xy_val)
:
  ConvertsM FB.conversion (do FB.and acc (←_root_.Clap.Lang.eq xy.1 xy.2)) state
    (acc_val && (xy_val.1 == xy_val.2)) True
:= by
  step _root_.Clap.Lang.eq.convertsM (FPair.converts_fst h_xy) (FPair.converts_snd h_xy) as cmp
  apply convertsM_of_convertsM (FB.and.convertsM h_acc h_cmp)
  . rfl
  . trivial

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a b : FVec p w}
  {a_vals b_vals : Vector (ZMod p) w}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
:
  ConvertsM FB.conversion (eq a b) state (decide (a_vals = b_vals)) True
:= by
  unfold eq

  step (FB.ofBool.convertsM (p := p) (b := true) (state := state)) as acc0

  have h_elems : ∀ i : Fin w,
      Converts FPair.conversion acc0_state (a.zip b)[i] ((a_vals.zip b_vals)[i]) :=
    fun i ↦ FVec.converts_zip h_a h_b i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc : Bool) (xy : ZMod p × ZMod p) ↦ acc && (xy.1 == xy.2))
      h_elems h_acc0 step_convertsM)
  . rw [← Vector.foldl_toList, Vector.toList_zip, foldl_and_all,
        zip_all_eq_decide (by simp)]
    simp [Vector.toList_inj]
  . trivial

end eq
end eq

end Clap.Lang.FVec
