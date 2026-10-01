import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Gate.share

namespace Clap.Lang

variable {p : ℕ}

section powers

/-- `[1, α, α², …, α^(n-1)]`, Circom's `challenge_powers` in `IsSubstring` and
`AssertIsConcatenation`. Every power after the first is shared, as each is a signal
(`challenge_powers[i] <== challenge_powers[i-1] * random_challenge`) there, so no expression's
degree grows with `n`.

`Vector.scanlM` also runs the step on the last element and drops the result, so this emits one
more `share` (of `α^n`) than Circom's `n - 1`. Nothing reads it. -/
def powers (α : F p) (n : ℕ) : ClapM p (FVec p n) := do
  let one ← mkF 1
  Vector.scanlM (fun acc a ↦ do
    let prod ← acc * a
    share prod) one (Vector.replicate n α)

namespace powers

private lemma step_convertsM
  {state : ClapMState p}
  {acc a : F p}
  {acc_val a_val : ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM F.conversion (do let prod ← acc * a; share prod) state (acc_val * a_val) True
:= by
  step mkMul.convertsM h_acc h_a as prod
  apply convertsM_of_convertsM (share.convertsM h_prod)
  . rfl
  . trivial

lemma convertsM
  {n : ℕ}
  {state : ClapMState p}
  {α : F p}
  {α_val : ZMod p}
  (h_α : Converts F.conversion state α α_val)
:
  ConvertsM FVec.conversion (powers α n) state (Vector.ofFn fun i : Fin n ↦ α_val ^ i.val) True
:= by
  unfold powers
  step mkF.convertsM as one
  have h_v : ∀ i : Fin n, Converts F.conversion one_state (Vector.replicate n α)[i]
      (Vector.replicate n α_val)[i] := by
    intro i
    simpa using h_α
  apply convertsM_of_convertsM
    (convertsM_scanlM (f_spec := fun acc a ↦ acc * a) h_v h_one step_convertsM)
  . ext i hi
    rw [Vector.getElem_scanl _ _ _ _ hi, Vector.getElem_ofFn]
    simp only [Vector.toList_replicate, List.take_replicate]
    rw [show min i n = i by omega]
    clear hi
    induction i with
    | zero => simp
    | succ i ih => rw [List.replicate_succ', List.foldl_append, ih]; simp [pow_succ]
  . trivial

end powers

end powers

section examples

/-! By evaluation, since every power is a `share` of an expression over the previous one, which
`Circuit.toWg` cannot yet generate a witness for (see the examples in
`Clap/Lang/Data/FString/asciiDigitsToScalar.lean`). -/

private abbrev q : ℕ := 65537

local instance instFactPrimePowersQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def powersOf (α : ZMod q) (n : ℕ) : List (Option (ZMod q)) :=
  let cmd : ClapM q (HashConsSt q × FVec q n) := do
    let a ← liftM (HashConsM.mkConstant (p := q) α)
    let r ← powers a n
    let σ ← getThe (HashConsSt q)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  r.2.toList.map fun e ↦ [Γ, r.1|e]

example : powersOf 3 5 = [some 1, some 3, some 9, some 27, some 81] := by native_decide
example : powersOf 7 1 = [some 1] := by native_decide
example : powersOf 7 0 = [] := by native_decide

end examples

end Clap.Lang
