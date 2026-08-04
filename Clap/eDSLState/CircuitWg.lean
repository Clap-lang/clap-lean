import Clap.eDSLState.Circuit

namespace Clap

section
/-
-- inductive Wg (p : ℕ) : Type where
--   | nil
--   | cons (_ : ZMod p) (_ : Wg p)
--   | input (_ : ZMod p → Wg p)

-- def Circuit.toWg (c : Circuitₑ p) : Wg p :=
--   match c with
--   | .nil => Wg.nil
--   | .eq0 _ c => c.toWg
--   | .lam k => Wg.input fun i => (k i).toWg
--   | .share e k =>
--     letI e := e.eval
--     .cons e (k e).toWg
--   | .isZero e k =>
--     letI e := e.eval
--     let o : ZMod p := if e = 0 then 1 else 0
--     .cons e⁻¹ (.cons o (k o).toWg)
--   | .num2bits w e c =>
--     letI bits := num2bitsLsbPure w (Exp.eval e)
--     List.foldr (fun b acc => .cons b acc) (c bits).toWg bits

-- def Wg.run {p : Nat} [Fact (Nat.Prime p)] (wg : Wg p) (ins : Array (ZMod p)) : Array (ZMod p) :=
--   match wg with
--   | .nil => #[]
--   | .cons x wg => ⟨x::(wg.run ins).toList⟩
--   | .input k =>
--     match ins with
--     | ⟨[]⟩ => #[]
--     | ⟨i::ins⟩ => #[i] ++ (k i).run ins.toArray
-/
end

structure Wg (p : ℕ) where
  data : List (ZMod p)
  numInputs : ℕ
  deriving Repr

def Wg.run {p : ℕ} (wg : Wg p) (varStore : VarStore p) : VarStore p := sorry

def Circuit.toWg {p : ℕ} (circuit : Circuit p) : VarStore p → VarStore p := sorry

section
-- inductive Cs (p : ℕ) (var : Type) : Type where
--   | nil
--   | eq0 (_ : Exp p var) (_ : Cs p var)
--   | lam (_ : var -> Cs p var)

-- def Circuit.toCs (c : Circuit p var) : Cs p var :=
--   match c with
--   | .nil =>
--       .nil
--   | .eq0 e c =>
--       .eq0 e c.toCs
--   | .lam k =>
--       .lam fun x => (k x).toCs
--   | .share e k =>
--       .lam fun o => .eq0 (e - .v o) (k o).toCs
--   | .isZero e k =>
--     .lam fun inv =>
--       .lam fun o =>
--         .eq0 (.c 1 - .v inv * e - .v o)
--           (.eq0 (.v o * e) (k o).toCs)
--      -- e=0          o=1
--      -- e≠0 inv=e^-1 o=0
--   | .num2bits w e c =>
--     Cs.curry w (fun bits =>
--       let ls := bits.toList
--       letI rest := (c bits.toList).toCs
--       letI rest := Cs.eq0 (bits2num_e ls - e) rest
--       assert_bits_e ls rest)

-- inductive Cs (p : ℕ) (var : Type) : Type where
--   | nil
--   | eq0 (_ : Exp p var) (_ : Cs p var)
--   | lam (_ : var -> Cs p var)

-- def eval : Circuitₑ p → denotation (ZMod p)
--   | .nil =>
--       .u
--   | .lam k =>
--       .l fun x => eval (k x)
--   | .eq0 e c =>
--       if e.eval = 0 then eval c else .n
--   | .share e k =>
--       (k e.eval).eval
--   | .isZero e k =>
--       if e.eval = 0 then (k 1).eval else (k 0).eval
--   | .num2bits w e k =>
--       if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n
end

opaque Cs : Type

def Cs.run {p : ℕ} (cs : Cs) (varStore : VarStore p) : Bool := true

def Circuit.toCs {p : ℕ} (circuit : Circuit p) : VarStore p → Bool := sorry

-- theorem soundness {c : Circuitₑ p} : circuitWF c → wrBisim c.eval c.toCs.eval

-- theorem completeness : circuitWF c → c.eval = (wrap c.toWg c.toCs).eval

end Clap
