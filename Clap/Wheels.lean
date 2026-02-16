import Lean
import Mathlib.Lean.Meta
import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Primes

namespace Clap

@[reducible]
def typ (a r : Type) : Nat → Type
  | 0     => r
  | n + 1 => a → typ a r n

@[reducible]
def curry {α β : Type} {n : Nat} (k : Vector α n → β) : typ α β n :=
  match n with
  | 0     => k #v[]
  | n + 1 => fun x => curry fun l => k ⟨⟨x :: l.toList⟩, by simp⟩

section

open Lean Meta

/--
This is abstracted over because the current implementation is the simplest approximation
that may (or may not) interfere with the context - if it does, it is easily fixable.

TODO(workaround) Currently a stopgap measure before we incorporate currying in a better way
The better way would involve systematically expressing `v : Vec n` as `#v[v[0], ... v[n-1]]`.
Thus, this will not be needed at all.
-/
def reduceCurry (goal : MVarId) : MetaM MVarId := goal.withContext do
  let ([goal], _) ← Elab.runTactic goal
    (←`(tactic|dsimp -zeta only
      [
        curry, Vector.toList_mk, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ,
        List.getElem_cons_zero
      ]))
    | throwError m!"`reduceCurry` failed in:\n{goal}"
  return goal

elab "reduce_curry" : tactic => Elab.Tactic.liftMetaTactic' reduceCurry

end

/-- Computes minimum number of bits necessary to represent the input. -/
def minBits (x : ℕ) : ℕ :=
  if x = 0 then 1 else
  let nb := Nat.log2 x
  if 2^nb ≤ x then nb + 1 else nb

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

end Clap

def Lean.Expr.foldlRecM {α : Type}
  {m : Type → Type} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  (f : α → Expr → m α) (init : α) (e : Expr) : m α :=
  (·.2) <$> (
    StateT.run (
      Meta.transform e <| fun e' ↦
        Functor.mapConst TransformStep.continue (get >>= monadLift ∘ flip f e' >>= set)
    ) init
  )

lemma ZMod.val_sum' {m n : ℕ} [NeZero n] {f : Fin m → ZMod n} :
    (∑ i, f i).val =  (∑ i, (f i).val) % n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ZMod.val_add, ih, Nat.add_mod_mod]

lemma ZMod.val_sum {n : ℕ} [NeZero n] {α : Type} [Fintype α] {f : α → ZMod n} :
    (∑ i, f i).val =  (∑ i, (f i).val) % n := by
  rcases Finite.exists_equiv_fin α with ⟨α_size, ⟨exists_bij⟩⟩
  let g := exists_bij.toFun
  let g_inv := exists_bij.invFun
  have h₁ {β : Type} [Semiring β] {f : α → β} : ∑ i, f i = ∑ i, f (g_inv i) := by
    refine Function.Bijective.finset_sum g (Equiv.bijective exists_bij) f (fun x => f (g_inv x)) ?_
    intros x
    simp only
    congr
    dsimp [g, g_inv]
    exact (Equiv.apply_eq_iff_eq_symm_apply exists_bij).mp rfl
  rw [h₁, h₁]
  exact val_sum'
