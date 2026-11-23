import Clap.Model.Monad

/-!
# Loops in `ClapM`

Mathlib's `WriterT` bind appends the gates of the
rest of the program after running it: `(fun (b, w₂) ↦ (b, w₁ ++ w₂)) <$> (f a).run`. So a
`for i in [0:n]` loop (and `List.mapM`, `Vector.ofFnM`, `foldlM`, …) keeps one stack frame per
iteration until the loop ends, and every `w₁ ++ w₂` copies all the gates emitted after it

`for i in loopRange n do …` iterates `i = 0, …, n - 1` as `for i in [0:n] do …` does, in constant
stack and linear time. the `ForIn (ClapM p) LoopRange ℕ` instance runs each step on `ClapM`'s raw
state and appends that step's gates to an accumulator

TODO:
`loopRange` only covers `for` loops. `Vector.mapM`, `List.mapM`, `Vector.ofFnM`, `foldlM`,
`Vector.scanlM`, recursion on a length and long straight-line `do` blocks still keep a frame per
bind and copy the gates after it.
-/

namespace Clap

/-- The indices `start, start + 1, …, stop - 1`, for `for i in loopRange stop do …` in `ClapM`. -/
structure LoopRange where
  start : ℕ
  stop : ℕ

/-- `for i in loopRange stop do …` is `for i in [start:stop] do …` without the stack frame and the
copy per step. -/
def loopRange (stop : ℕ) (start : ℕ := 0) : LoopRange := ⟨start, stop⟩

namespace ClapM

variable {p : ℕ} {β : Type}

/-- Steps `i, i + 1, …, stop - 1` of a `LoopRange` loop: step `i` runs `f i b` from `numAlloc` and
`σ`, and its gates go after `acc`. Tail-recursive. -/
def loopRangeGo (stop : ℕ) (f : ℕ → β → ClapM p (ForInStep β)) (i : ℕ) (b : β) (acc : Circuit)
    (numAlloc : ℕ) (σ : HashConsSt p) : ((β × Circuit) × ℕ) × HashConsSt p :=
  if i < stop then
    let (((step, gates), numAlloc), σ) := (f i b).run numAlloc σ
    match step with
    | .done b => (((b, acc ++ gates), numAlloc), σ)
    | .yield b => loopRangeGo stop f (i + 1) b (acc ++ gates) numAlloc σ
  else (((b, acc), numAlloc), σ)
termination_by stop - i

instance : ForIn (ClapM p) LoopRange ℕ where
  forIn r init f := show ClapM p _ from fun numAlloc σ ↦ loopRangeGo r.stop f r.start init #[] numAlloc σ

section Proofs

variable {α : Type}

theorem run_pure' (a : α) (numAlloc : ℕ) (σ : HashConsSt p) :
    (pure a : ClapM p α).run numAlloc σ = (((a, #[]), numAlloc), σ) := rfl

theorem run_bind' (x : ClapM p α) (g : α → ClapM p β) (numAlloc : ℕ) (σ : HashConsSt p) :
    (x >>= g).run numAlloc σ =
      let (((a, c₁), n₁), σ₁) := x.run numAlloc σ
      let (((b, c₂), n₂), σ₂) := (g a).run n₁ σ₁
      (((b, c₁ ++ c₂), n₂), σ₂) := rfl

theorem loopRangeGo_eq (stop : ℕ) (f : ℕ → β → ClapM p (ForInStep β)) (i : ℕ) (b : β)
    (acc : Circuit) (numAlloc : ℕ) (σ : HashConsSt p) :
    loopRangeGo stop f i b acc numAlloc σ =
      let (((b', c), n), σ') := (forIn (List.range' i (stop - i)) b f).run numAlloc σ
      (((b', acc ++ c), n), σ') := by
  induction hn : stop - i generalizing i b acc numAlloc σ with
  | zero =>
    rw [loopRangeGo, if_neg (by omega)]
    simp [run_pure']
  | succ n ih =>
    rw [loopRangeGo, if_pos (by omega), List.range'_succ, List.forIn_cons, run_bind']
    rcases hr : (f i b).run numAlloc σ with ⟨⟨⟨step, gates⟩, n₁⟩, σ₁⟩
    cases step with
    | done b' => simp [run_pure']
    | yield b' =>
      simp only
      rw [ih (i + 1) b' (acc ++ gates) n₁ σ₁ (by omega)]
      simp [Array.append_assoc]

/-- `for i in loopRange stop start` runs the steps of `for i in List.range' start (stop - start)`. -/
theorem forIn_loopRange (r : LoopRange) (init : β) (f : ℕ → β → ClapM p (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start (r.stop - r.start)) init f := by
  funext numAlloc σ
  change loopRangeGo r.stop f r.start init #[] numAlloc σ = _
  rw [loopRangeGo_eq]
  rcases h : (forIn (List.range' r.start (r.stop - r.start)) init f).run numAlloc σ
    with ⟨⟨⟨b, c⟩, n⟩, σ'⟩
  simp only [Array.empty_append]
  exact h.symm

/-- `for i in loopRange stop start` is `for i in [start:stop]`. -/
theorem forIn_loopRange_eq_forIn_range (start stop : ℕ) (init : β)
    (f : ℕ → β → ClapM p (ForInStep β)) :
    forIn (loopRange stop start) init f = forIn [start:stop] init f := by
  rw [forIn_loopRange, Std.Legacy.Range.forIn_eq_forIn_range']
  simp [loopRange, Std.Legacy.Range.size]

end Proofs

end ClapM

end Clap
