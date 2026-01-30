import Lean
import Mathlib.Lean.Meta
import Mathlib.FieldTheory.Finite.Basic -- field operations

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

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Computes the `n` bit binary representation of `f`.
    If `n < minBits f` the result is truncated.
    If `n > minBits f` the result is padded with zeros.
-/
def num2bits_pure (n:ℕ) (f:ZMod p) : List (ZMod p) :=
  match n with
  | 0 => []
  | n+1 =>
    let bit := f % 2
    let rem := f / 2
    bit::(num2bits_pure n rem)

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
