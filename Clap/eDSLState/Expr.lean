import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.HashConsM
import Clap.eDSLState.HashCons.HashConsSt

namespace Clap

abbrev ValueCache (p : ℕ) := Array (Option (ZMod p))

@[grind cases]
structure Expr (p : ℕ) where
  ref : ExprRef
  σ : HashConsSt p

namespace Expr

section Expr

variable {p : ℕ} {e : Expr p}

@[grind =]
def deref (e : Expr p) : Option (CacheExpr p) := e.σ.exprs[e.ref]?

/--
Dereference is valid.
-/
@[grind =]
def wellFormed (e : Expr p) : Prop := e.ref < e.σ.size

instance : Decidable (wellFormed e) := inferInstanceAs <| Decidable (e.ref < e.σ.size)

prefix:max "*" => deref

@[grind _=_]
lemma wellFormed_iff_isSome : e.wellFormed ↔ (*e).isSome := by grind

@[grind →]
lemma wellFormed_frame {e' : Expr p}
  (h₁ : e.wellFormed) (h₂ : e.σ.exprs.isPrefixOf e'.σ.exprs) (h₃ : e.ref = e'.ref) : e'.wellFormed := by
  have : e.σ.exprs.toList.isPrefixOf e'.σ.exprs.toList = true := by grind
  grind [List.prefix_iff_getElem?]

end Expr

end Expr

end Clap
