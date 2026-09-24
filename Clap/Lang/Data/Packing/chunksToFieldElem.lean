import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

section chunksToFieldElem

/-- The field element that little-endian chunks of `bitsPerChunk` bits denote,
`vals[0] + 2^bitsPerChunk * vals[1] + …`, in Horner form. The ideal value of
`chunksToFieldElem`, named so the specifications built on it stay readable. -/
def chunksToNum {w : ℕ} (bitsPerChunk : ℕ) (vals : Vector (ZMod p) w) : ZMod p :=
  vals.reverse.foldl (fun acc x ↦ x + 2 ^ bitsPerChunk * acc) 0

/-- Pack `w` chunks of `bitsPerChunk` bits into one field element, chunk `0` least significant. -/
def chunksToFieldElem {w : ℕ} (bitsPerChunk : ℕ) (chunks : FVec p w) : ClapM p (F p) := do
  let acc0 ← mkF 0
  chunks.reverse.foldlM (fun acc x ↦ do
    let base ← mkF (2 ^ bitsPerChunk)
    let shifted ← base * acc
    x + shifted) acc0

namespace chunksToFieldElem

private lemma step_convertsM
  {bitsPerChunk : ℕ}
  {state : ClapMState p}
  {acc x : F p}
  {acc_val x_val : ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_x : Converts F.conversion state x x_val)
:
  ConvertsM F.conversion
    (do
      let base ← mkF (2 ^ bitsPerChunk)
      let shifted ← base * acc
      x + shifted)
    state (x_val + 2 ^ bitsPerChunk * acc_val) True
:= by
  step mkF.convertsM as base
  step mkMul.convertsM h_base h_acc as shifted
  apply convertsM_of_convertsM (mkAdd.convertsM h_x h_shifted)
  . rfl
  . trivial

lemma convertsM
  {w bitsPerChunk : ℕ}
  {state : ClapMState p}
  {chunks : FVec p w}
  {vals : Vector (ZMod p) w}
  (h_chunks : Converts FVec.conversion state chunks vals)
:
  ConvertsM F.conversion (chunksToFieldElem bitsPerChunk chunks) state
    (chunksToNum bitsPerChunk vals) True
:= by
  unfold chunksToFieldElem

  step mkF.convertsM as acc0

  have h_elems : ∀ i : Fin w,
      Converts F.conversion acc0_state chunks.reverse[i] vals.reverse[i] :=
    fun i ↦ FVec.converts_getElem (FVec.converts_reverse h_chunks) i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc x : ZMod p) ↦ x + 2 ^ bitsPerChunk * acc)
      h_elems h_acc0 step_convertsM)
  . rfl
  . trivial

end chunksToFieldElem

/-- `chunksToNum` over `ℕ`: the base-`2 ^ b` numeral of the chunks' values. -/
private def chunksToNat (b : ℕ) (l : List (ZMod p)) : ℕ :=
  l.foldr (fun x acc ↦ x.val + 2 ^ b * acc) 0

private lemma chunksToNat_lt {b : ℕ} {l : List (ZMod p)} (h : ∀ x ∈ l, x.val < 2 ^ b) :
    chunksToNat b l < 2 ^ (b * l.length) := by
  induction l with
  | nil => simp [chunksToNat]
  | cons x l ih =>
    simp only [chunksToNat, List.foldr_cons, List.length_cons] at ih ⊢
    have hx := h x (by simp)
    have hl := ih (fun y hy ↦ h y (by simp [hy]))
    calc x.val + 2 ^ b * l.foldr (fun x acc ↦ x.val + 2 ^ b * acc) 0
        < 2 ^ b + 2 ^ b * l.foldr (fun x acc ↦ x.val + 2 ^ b * acc) 0 := by omega
      _ = 2 ^ b * (l.foldr (fun x acc ↦ x.val + 2 ^ b * acc) 0 + 1) := by ring
      _ ≤ 2 ^ b * 2 ^ (b * l.length) := Nat.mul_le_mul_left _ hl
      _ = 2 ^ (b * (l.length + 1)) := by rw [← pow_add]; ring_nf

private lemma chunksToNat_cast [NeZero p] (b : ℕ) (l : List (ZMod p)) :
    (chunksToNat b l : ZMod p) = l.foldr (fun x acc ↦ x + 2 ^ b * acc) 0 := by
  induction l with
  | nil => simp [chunksToNat]
  | cons x l ih => simp only [chunksToNat, List.foldr_cons] at ih ⊢; push_cast [ih]; simp

private lemma chunksToNat_inj [NeZero p] {b : ℕ} :
    ∀ {l₁ l₂ : List (ZMod p)}, l₁.length = l₂.length →
      (∀ x ∈ l₁, x.val < 2 ^ b) → (∀ x ∈ l₂, x.val < 2 ^ b) →
      chunksToNat b l₁ = chunksToNat b l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | x₁ :: l₁, x₂ :: l₂, h_len, h₁, h₂, h => by
    simp only [chunksToNat, List.foldr_cons] at h
    have hx₁ := h₁ x₁ (by simp)
    have hx₂ := h₂ x₂ (by simp)
    have h_pos : 0 < 2 ^ b := Nat.two_pow_pos b
    have h_mod := congrArg (· % 2 ^ b) h
    have h_div := congrArg (· / 2 ^ b) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx₁, Nat.mod_eq_of_lt hx₂] at h_mod
    simp only [Nat.add_mul_div_left _ _ h_pos, Nat.div_eq_of_lt hx₁, Nat.div_eq_of_lt hx₂,
      zero_add] at h_div
    rw [ZMod.val_injective p h_mod,
      chunksToNat_inj (by simpa using h_len) (fun y hy ↦ h₁ y (by simp [hy]))
        (fun y hy ↦ h₂ y (by simp [hy])) h_div]

/-- Chunks below `2 ^ b` are determined by what they pack to, as long as all `w * b` bits fit
below `p`, so the packing never wraps. -/
lemma chunksToNum_injective {w b : ℕ} (h_fit : 2 ^ (w * b) ≤ p) {v₁ v₂ : Vector (ZMod p) w}
    (h₁ : ∀ i : Fin w, v₁[i].val < 2 ^ b) (h₂ : ∀ i : Fin w, v₂[i].val < 2 ^ b)
    (h : chunksToNum b v₁ = chunksToNum b v₂) : v₁ = v₂ := by
  haveI : NeZero p := ⟨by have := Nat.two_pow_pos (w * b); omega⟩
  have h_mem : ∀ {v : Vector (ZMod p) w}, (∀ i : Fin w, v[i].val < 2 ^ b) →
      ∀ x ∈ v.toList, x.val < 2 ^ b := by
    intro v hv x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa using hv ⟨i, by simpa using hi⟩
  have h_lt : ∀ {v : Vector (ZMod p) w}, (∀ i : Fin w, v[i].val < 2 ^ b) →
      chunksToNat b v.toList < p := fun hv ↦
    lt_of_lt_of_le (by simpa [Nat.mul_comm] using chunksToNat_lt (h_mem hv)) h_fit
  have h_eq : ∀ v : Vector (ZMod p) w, chunksToNum b v = (chunksToNat b v.toList : ZMod p) := by
    intro v
    rw [chunksToNat_cast, chunksToNum, ← Vector.foldl_toList, Vector.toList_reverse,
      List.foldl_reverse]
  rw [h_eq, h_eq, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (h_lt h₁),
    Nat.mod_eq_of_lt (h_lt h₂)] at h
  exact Vector.toList_inj.mp (chunksToNat_inj (by simp) (h_mem h₁) (h_mem h₂) h)

end chunksToFieldElem

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeChunksToFieldElemQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check {w : ℕ} (b : ℕ) (chunks : Vector (ZMod q) w) (expected : ZMod q) :
    ClapM q Unit := do
  let cs ← chunks.mapM mkF
  let r ← chunksToFieldElem b cs
  assert_eq r (← mkF expected)

private def sat {w : ℕ} (b : ℕ) (chunks : Vector (ZMod q) w) (expected : ZMod q) : Bool :=
  let c := check b chunks expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat 2 #v[] 0 = true := by native_decide
-- `[00₂, 11₂, 10₂] ↦ 101100₂`
example : sat 2 #v[0, 3, 2] 44 = true := by native_decide
example : sat 2 #v[0, 3, 2] 45 = false := by native_decide

end examples

end Clap.Lang.Packing
