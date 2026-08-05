import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels

namespace Clap

abbrev ExprRef := ℕ

instance {coll elem valid} [GetElem coll ℕ elem valid] :
  GetElem coll ExprRef elem valid := inferInstanceAs (GetElem coll ℕ elem valid)

instance {coll elem valid} [GetElem? coll ℕ elem valid] :
  GetElem? coll ExprRef elem valid := inferInstanceAs (GetElem? coll ℕ elem valid)

inductive BinaryOp
  | add
  | sub
  | mul
deriving BEq, Hashable, ReflBEq, LawfulBEq, Repr

instance {p} : Hashable (ZMod p) where
  hash x := UInt64.ofNat x.val

inductive CacheExpr (p : ℕ)
  | c (_ : ZMod p)
  | v (idx : ℕ)
  | binary_op (lhs rhs : ExprRef) (op : BinaryOp)
deriving BEq, Hashable, ReflBEq, LawfulBEq, Repr

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

@[aesop unsafe, grind .]
lemma wellFormed_binary_op_of_lt_lt {p} {n : ℕ} {lhs rhs op} (h₁ : lhs < n) (h₂ : rhs < n) :
  (CacheExpr.binary_op (p := p) lhs rhs op).wellFormed n := by
  aesop (add simp CacheExpr.wellFormed)

end Clap
