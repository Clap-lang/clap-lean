import Clap.Circuit

open Clap

/-
  Strong bisimulation, eventually.
  Relaxes `s_bisim` by allowing a player to continue moving, even if
  the other as already failed, provided that it will also fail
  eventually.
  This can be useful if constraints are shuffled and a failing input
  triggers at different times.
  Not used so far.
-/
inductive s_bisim_eventually : (l r: denotation) -> Prop where
  | none
      : s_bisim_eventually .n .n
  | unit
      : s_bisim_eventually .u .u
  | lam
      (kl kr:F -> denotation)
      (h: ∀ x, s_bisim_eventually (kl x) (kr x))
      : s_bisim_eventually (.l kl) (.l kr)
  | left
      (kl:F -> denotation)
      (h: ∀ x, s_bisim_eventually (kl x) .n)
      : s_bisim_eventually (.l kl) .n
  | right
      (kr:F -> denotation)
      (h: ∀ x, s_bisim_eventually .n (kr x))
      : s_bisim_eventually .n (.l kr)

lemma s_bisim_eventually_rfl : ∀ c,
  s_bisim_eventually c c := by
  intro c
  induction c with
  | u => constructor
  | n => constructor
  | l k h =>
    constructor
    exact h

theorem s_bisim_eventually_symm : ∀ c1 c2,
  s_bisim_eventually c1 c2 -> s_bisim_eventually c2 c1 := by
  intro c1
  induction c1 with
  | u =>
    intro c2 h
    cases c2
    repeat (first | contradiction | constructor )
  | n =>
    intro c2 h12
    induction c2 with
    | u => contradiction
    | n => constructor
    | l k2 h21 =>
      constructor
      intro x
      apply h21
      cases h12
      case n.l.h.h12.right h =>
        apply h
  | l k hl =>
    intro c2 h12
    induction c2 with
    | u => contradiction
    | n =>
      constructor
      intro x
      apply hl
      cases h12
      case l.n.h.a.left h =>
        apply h
    | l k2 h2 =>
      constructor
      intro x
      apply hl
      cases h12
      case l.l.h.a.lam h =>
        apply h

theorem s_bisim_eventually_trans : ∀ c1 c2 c3,
  (bis12: s_bisim_eventually c1 c2) -> (bis23: s_bisim_eventually c2 c3) -> s_bisim_eventually c1 c3 := by
  sorry

instance : Setoid denotation where
  r := s_bisim_eventually
  iseqv := {
    refl := s_bisim_eventually_rfl
    symm := @s_bisim_eventually_symm
    trans := @s_bisim_eventually_trans
  }
