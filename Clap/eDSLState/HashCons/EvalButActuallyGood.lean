import Clap.eDSLState.HashCons.HashConsM

namespace Clap.HashConsM

abbrev ValueCache (p : ℕ) := Array (Option (ZMod p))

def evalCore {p} (Γ : VarStore p) (expr : CacheExpr p) (cache : ValueCache p) : Option (ZMod p) :=
  match expr with
  | .c k => .some k
  | .v idx => Γ[idx]?
  | .binary_op lhs rhs op =>
    let op := match op with
              | .add => (· + ·)
              | .sub => (· - ·)
              | .mul => (· * ·)
    let lhs := cache[lhs]!
    let rhs := cache[rhs]!
    op <$> lhs <*> rhs

def evalWithCache {p}
  (varStore : VarStore p) (e : ExprRef) (cache : ValueCache p) (σ : HashConsSt p) : ValueCache p :=
  if e < cache.size
  then cache
  else
    match σ[cache.size]? with
    | .none => cache
    | .some expr =>
      let val := evalCore varStore expr cache
      evalWithCache varStore e (cache.push val) σ
  termination_by (e + 1) - cache.size
  decreasing_by grind

def state : HashConsSt 37 where
  exprs := #[
    .c 3,
    .c 2,
    .binary_op 0 1 .add
  ]
  wellFormed := by decide

#eval evalWithCache {} 2 #[] state

def eval {p} (varStore : VarStore p) (e : ExprRef) (σ : HashConsSt p) : Option (ZMod p) :=
  (evalWithCache varStore e #[] σ)[e]!

notation "[" varStore "," state "|" x "]" => eval varStore x state

abbrev evalM {p} (varStore : VarStore p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  let expr ← e
  let state ← get
  return [varStore,state|expr]

notation "[" varStore "," state "|" "←" x "]" => HashConsM.run (evalM varStore x) state

section Prefix

lemma Array.size_eq_zero_of_isPrefixOf_size_eq_zero
  {T} [BEq T] [LawfulBEq T]
  (a b: Array T)
  (h_prefix : a.isPrefixOf b = true)
  (h_size : b.size = 0)
:
  a.size = 0
:= by
  rewrite [←Array.isPrefixOf_toList] at h_prefix
  grind

lemma evalCache_of_lt_prefix
  {p : ℕ}
  {varStore : VarStore p}
  {e : ExprRef}
  {cache : ValueCache p}
  {σ σ' : HashConsSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_lt_prefix : e < σ.exprs.size)
:
  evalWithCache varStore e cache σ =
  evalWithCache varStore e cache σ'
:= by
  induction h: e + 1 - cache.size generalizing cache with
  | zero =>
    unfold evalWithCache
    grind
  | succ n ih =>
    unfold evalWithCache
    split_ifs
    . rfl
    . have : cache.size < σ.exprs.size := by grind
      have : σ[cache.size]? = σ'[cache.size]? := by
        simp
        rewrite [←Array.getElem?_toList, ←Array.getElem?_toList]
        have : σ.exprs.toList.isPrefixOf σ'.exprs.toList = true := by grind
        have : σ.exprs.toList <+: σ'.exprs.toList := by grind
        have := List.prefix_iff_getElem?.mp this cache.size (by grind)
        grind
      rewrite [this]
      split
      . rfl
      . simp
        apply ih
        grind



end Prefix

end Clap.HashConsM
