import Clap.Circuit

import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels

namespace Clap

abbrev ExprRef := ℕ

inductive BinaryOp
  | add
  | sub
  | mul
deriving BEq, Hashable, ReflBEq, LawfulBEq

inductive CacheExpr (p : ℕ)
  | c (_ : ZMod p)
  | v (idx : ℕ)
  | binary_op (lhs rhs : ExprRef) (op : BinaryOp)
deriving BEq, Hashable, ReflBEq, LawfulBEq

def CacheExpr.wellFormed {p : ℕ} (e : CacheExpr p) (idx : ExprRef) : Prop :=
  match e with
    | c _ => True
    | v _ => True
    | binary_op lhs rhs _ =>
      lhs < idx ∧
      rhs < idx

instance {p} {e : CacheExpr p} {idx : ExprRef} : Decidable (CacheExpr.wellFormed e idx) := by
  unfold CacheExpr.wellFormed
  split <;> infer_instance

@[simp, grind .]
lemma wellFormed_c {p} {k : ZMod p} {n : ℕ} : (CacheExpr.c k).wellFormed n := trivial

@[simp, grind .]
lemma wellFormed_v {p} {idx : ℕ} {n : ℕ} : (CacheExpr.v (p := p) idx).wellFormed n := trivial


end Clap
