import Clap.Compiler.Back.Cs
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.FpMul
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Wg


namespace Clap

/-

  Soundness.
  In order to show that a Cs is not more accepting that its original
  Circuit, i.e. that it won't accept more inputs, we show that there
  is a right-weak bisimulation `wrBisim` between them.
  In particular, while a Circuit evaluates to any of the `denotation`
  values, a Cs might be stuck waiting for an extra input. Therefore
  the Cs is allowed to receive any value as extra input while the
  Circuit "waits" for the Cs to catch up, so long as they end up two
  denotations that bisimulate as well.

  A circuit can also be compiled to a Wg for Witness Generator using
  the `to_wg` function. A Wg computes the values needed by a Cs to
  check any computation that was done by the Circuit.

  Completeness
  A Cs and Wg can be composed using `wrap` to obtain a new Cs that
  does not require extra inputs compared to its original Circuit, as
  all extra inputs are immediately filled by the Wg.
  In order to show that Wg and Cs work correctly together, we show
  that, once wrapped, they are equivalent to the original Circuit.
-/

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

def Circuit.toCs (c : Circuit p var) : Cs p var :=
  match c with
  | .nil =>
      .nil
  | .eq0 e c =>
      .eq0 e c.toCs
  | .lam k =>
      .lam fun x => (k x).toCs
  | .share e k =>
      .lam fun o => .eq0 (e - .v o) (k o).toCs
  | .isZero e k =>
    IsZero.isZero_circuit e (fun i ↦ (k i).toCs)
     -- e=0          o=1
     -- e≠0 inv=e^-1 o=0
  | .num2bits w e c =>
    Num2Bits.num2bits_circuit w e (fun bits => (c bits.toList).toCs)
  | .fpmul w _ a b p' cont =>
    FpMul.fpMul_circuit w a b p' (fun i ↦ (cont i).toCs)

def toCs' (c : Circuit' p) : Cs' p := fun var => (c var).toCs

-- example {w k : ℕ} : k > 0 → w > 0 → (2 ^ (2*w + 1) * k) > (2^(2*w)*k + 2^w) := by
--   intros h h'
--   ring_nf
--   rw [Nat.mul_two]
--   apply fun a_1 => Nat.add_lt_add_left a_1 _
--   apply lt_mul_of_one_le_of_lt (Nat.one_le_of_lt h)
--   exact (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)

def Circuit.toWg (c : Circuitₑ p) : Wg p :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c => c.toWg
  | .lam k => Wg.input fun i => (k i).toWg
  | .share e k =>
    letI e := e.eval
    .cons e (k e).toWg
  | .isZero e k =>
    letI e := e.eval
    let o : ZMod p := if e = 0 then 1 else 0
    .cons e⁻¹ (.cons o (k o).toWg)
  | .num2bits w e c =>
    Num2Bits.num2bits_wg w e (fun ls => (c ls).toWg)
  | .fpmul w k a b p' cont =>
    FpMul.fpmul_wg w k a b p' (fun i => (cont i).toWg)


def toWg' (c:Circuit' p) : Wg p := (c (ZMod p)).toWg

def Wg.run {p : Nat} [Fact (Nat.Prime p)] (wg : Wg p) (ins : Array (ZMod p)) : Array (ZMod p) :=
  match wg with
  | .nil => #[]
  | .cons x wg => ⟨x::(wg.run ins).toList⟩
  | .input k =>
    match ins with
    | ⟨[]⟩ => #[]
    | ⟨i::ins⟩ => #[i] ++ (k i).run ins.toArray

def wrap (wg : Wg p) (cs : Cs p (ZMod p)) : Cs p (ZMod p) :=
  match wg,cs with
  |         .nil , .nil      => .nil
  |           wg , .eq0 e cs => .eq0 e (wrap wg cs)
  | Wg.input kwg , .lam k    => .lam fun x => wrap (kwg x) (k x)
  |   .cons x wg , .lam k    => wrap (wg : Wg p) (k x)
  |            _ , _         => .eq0 (.c 1) .nil -- needed because we don't have typed wg and cs

open Simulation


omit inst' in
lemma foldr_curry {n : ℕ} {ls : List (ZMod p)} {wg : Wg p} {f : Vector (ZMod p) n → Cs p (ZMod p)}
    (h : ls.length = n) : wrap (List.foldr (fun b acc => Wg.cons b acc) wg ls) (Cs.curry n f) =
      wrap wg (f ⟨⟨ls⟩, h⟩) := by
  revert ls
  induction n with
  | zero =>
    intros ls h
    simp [List.eq_nil_iff_length_eq_zero.mpr h]
  | succ n ih =>
    intros ls h
    rcases List.exists_cons_of_length_eq_add_one h with ⟨l, ls', h'⟩
    simp only [h', List.foldr_cons]
    rw (occs := .pos [1]) [wrap, ih (by aesop)]
    rfl
