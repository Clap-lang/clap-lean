import Clap.Circuit
import Clap.Lang
import Mathlib.Control.Monad.Cont

namespace Clap

namespace Circuit

section

variable {var : Type} {p : ℕ}

def pretty [Repr var] [Index var] (c : Circuit p var) := repr 0 c

def printUsing [Repr var] [BEq var] [Hashable var]
               (Γ : Std.HashMap var String) (c : Circuit p var) : Std.Format :=
  go 0 c
  where go (l : ℕ) (c : Circuit p var) :=
    letI next (l : ℕ) (k : var → Circuit p var) := repr (l+1) (k (index l))
    letI gos (w l : ℕ) (k : List var → Circuit p var) := repr (l+w) (k ((List.range w).map index))
    match c with
    | .nil => "nil"
    | .lam k => s!"λ{l} {next l k}"
    | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"
    | .share e k => s!"share {_root_.repr e} {next l k}"
    | .isZero e k => s!"fun _ ↦ isZero {_root_.repr e} {next l k}"
    | .num2bits w e k => s!"num2bits {w} {_root_.repr e} {gos w l k}"

end Circuit

end

namespace Edsl

section

variable {p : ℕ}

abbrev CircuitContM (p : ℕ) (α : Type) : Type := Cont (Circuitₑ p) α

def CircuitContM.run {α : Type} (m : CircuitContM p α) : Circuitₑ p :=
  ContT.run m fun _ ↦ .nil

@[irreducible]
def eq0 (e : ZMod p) : CircuitContM p Unit := fun c ↦
  Clap.Circuit.eq0 e (c ())

@[irreducible]
def lam : CircuitContM p (ZMod p) :=
  Clap.Circuit.lam

@[irreducible]
def share (e : ZMod p) : CircuitContM p (ZMod p) :=
  Clap.Circuit.share e

@[irreducible]
def isZero (e : ZMod p) : CircuitContM p (ZMod p) :=
  Clap.Circuit.isZero e

@[irreducible]
def num2bits (w : ℕ) (e : ZMod p) : CircuitContM p (List (ZMod p)) :=
  Clap.Circuit.num2bits w e

end

end Edsl

namespace Examples

def TestPrime := 521

instance : Fact (Nat.Prime TestPrime) := ⟨by native_decide⟩

instance : Circuit.Index (ZMod TestPrime) := ⟨fun x ↦ (x : ZMod _)⟩

section

open Lang Edsl

variable {p : ℕ} {α β : Type}

namespace EvalRandom

def random (a : FB p) : CircuitContM p (FB p) := do
  let a ← share a
  let b ← share (a + 4)
  let c ← num2bits 4 b
  eq0 b
  discard ([1, 2, 3].mapM eq0)
  return c[0]!

def thisIsIndeedACircuit : CircuitContM p Unit := do
  let a ← random 5
  eq0 a

-- /-- info: share 42 share 4 num2bits 4 2 eq0 1 eq0 1 eq0 2 eq0 3 nil -/
-- #guard_msgs in
#eval thisIsIndeedACircuit.run.pretty (p := TestPrime)

end EvalRandom

namespace LessThan

def lessThan_aux (w : ℕ) (a b : F p) : CircuitContM p (FB p) := do
  let d := a - b + 2^w
  let d ← num2bits (w + 1) d
  return FB.not d[w]!

def lessThan (a b : F8 p) : CircuitContM p (FB p) := do
  lessThan_aux 8 a b

/-- info: num2bits 9 257 nil -/
#guard_msgs in
#eval (lessThan (3 : F8 TestPrime) 2).run.pretty

lemma CircuitContM.pure_def {x : α} : (pure x : CircuitContM p α) = fun f ↦ f x := rfl
lemma CircuitContM.bind_def {x : CircuitContM p α} {f : α → CircuitContM p β} :
  bind (m := CircuitContM p) x f = fun g => x fun i => f i g := rfl

@[simp]
lemma num2bits_eq_num2bitsLsbPure {w} {a b} :
  Edsl.num2bits (w+1) (a - b + (2^w : ZMod p)) =
  Circuit.num2bits (w + 1) (Exp.c (a - b + 2 ^ w)) := by
  unfold Edsl.num2bits
  rfl

def abc {α} : FB p → CircuitContM p α := sorry

def lessThan_equiv [Fact (Nat.Prime p)] {w} {a b : F p}
  (ha : a.val < 2^w)
  (hb : b.val < 2^w)
  (hw : 2^(w+1) < p) :
  lessThan_aux w a b = abc (FB.ofBool (a.val < b.val)) := by
  have hp : p ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.Prime.pos Fact.out)
  haveI : NeZero p := ⟨hp⟩
  have h2w_lt_p : 2^w < p :=
    lt_trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self w)) hw
  have h2w_val : (2^w : ZMod p).val = 2^w := by
    have : (2^w : ZMod p) = ((2^w : ℕ) : ZMod p) := by norm_cast
    rw [this]; exact ZMod.val_cast_of_lt h2w_lt_p
  have h_a_plus_2w : (a + (2^w : ZMod p)).val = a.val + 2^w := by
    have h := ZMod.val_add_of_lt (a := a) (b := (2^w : ZMod p)) (by rw [h2w_val]; omega)
    rw [h2w_val] at h; exact h
  have hd_val : (a - b + (2^w : ZMod p)).val = a.val + 2^w - b.val := by
    have heq : a - b + (2^w : ZMod p) = a + (2^w : ZMod p) - b := by ring
    rw [heq, ZMod.val_sub (by rw [h_a_plus_2w]; omega), h_a_plus_2w]
  have hd_lt : (a - b + (2^w : ZMod p)).val < 2^(w+1) := by
    rw [hd_val]
    have h : 2^(w+1) = 2^w + 2^w := by ring
    omega
  unfold lessThan_aux
  dsimp
  rw [num2bits_eq_num2bitsLsbPure]
  ext f

  rw [CircuitContM.bind_def]
  simp [ContT.run, Id.run]
  
  -- show Option.bind (num2bits (w+1) (a - b + 2^w)) (fun d => some (FB.not d[w]!)) =
  --      some (FB.ofBool (a.val < b.val))
  -- rw [hnum2bits, Option.bind_some]
  rw [getElem!_pos (num2bitsLsbPureV (w+1) (a - b + (2^w : ZMod p))) w (Nat.lt_succ_self w),
      num2bitsLsbPureV_getElem_val (a - b + (2^w : ZMod p)) (w+1) w (Nat.lt_succ_self w)]
  by_cases hab : a.val < b.val
  · have hzero : (a - b + (2^w : ZMod p)).val / 2^w = 0 :=
      Nat.div_eq_of_lt (by rw [hd_val]; omega)
    simp [hzero, FB.not, FB.ofBool, FB.true,
          show (decide (a.val < b.val) : Bool) = true from decide_eq_true_eq.mpr hab]
  · push_neg at hab
    have hone : (a - b + (2^w : ZMod p)).val / 2^w = 1 := by
      apply Nat.div_eq_of_lt_le
      · simp; rw [hd_val]; omega
      · rw [hd_val]
        have h : 2 * 2^w = 2^(w+1) := by ring
        omega
    simp [hone, FB.not, FB.ofBool, FB.false,
          show (decide (a.val < b.val) : Bool) = false from
            decide_eq_false_iff_not.mpr (Nat.not_lt.mpr hab)]



-- open Clap.Lang.Spec.F8 in
-- lemma lessThan_equiv [Fact (Nat.Prime p)] {a b : F p}
--   (ha : valid a) (hb : valid b) (hw : 2^(8+1) < p) :
--   lessThan a b = pure (FB.ofBool (toUInt8 a < toUInt8 b)) := by
--   unfold lessThan lessThan_aux
--   simp_rw [CircuitContM.pure_def, CircuitContM.bind_def]
--   ext cont
--   suffices
--     (Edsl.num2bits (8 + 1) (a - b + 2 ^ 8) fun i => cont (FB.not i[8]!)) =
--     cont (FB.ofBool (decide (toUInt8 a < toUInt8 b))) by simpa
  
--   dsimp

--   simp_all [valid, Nat.reducePow, Nat.reduceAdd, toUInt8, UInt8.lt_iff_toNat_lt,
--     UInt8.toNat_ofNat', Nat.mod_eq_of_lt]
  
  
--   rw [CircuitContM.pure_def]
--   simp only [Id.run, ContT.run, id_eq]
--   rw [map_eq_bind_pure_comp]
--   rw [CircuitContM.bind_def]
--   simp [pure]
  
  

  

  

end

end LessThan

end Examples

end Clap
