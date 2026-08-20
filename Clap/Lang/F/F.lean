import Clap.eDSLState.eDSL
import Clap.eDSLState.IsValid

import Clap.Lang.Wheels

namespace Clap.Lang

abbrev F := ExprRef -- TODO Expr or ExprRef?
abbrev FB := F

namespace F

variable {p : ℕ}

instance : IsValid p F where
  isValid Γ σ x := [Γ,σ|x].isSome = true

open HashConsM in
def eq {p : ℕ} [p.AtLeastTwo] (a b : F) : ClapM p FB := do
  isZero (←mkSub (p := p) a b)

open HashConsM in
def oneHotRaw [p.AtLeastTwo] (len : ℕ) (idx : F) : ClapM p (Vector FB len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ do
    let idx_val ← mkConstant (p := p) i
    F.eq idx idx_val
  )

def matches_spec
  [p.AtLeastTwo]
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {α β}
  (toIdeal : VarStore p → HashConsSt p → α → Option β)
  (cmd : ClapM p α)
  (spec : β)
: Prop :=
  let result := cmd.getResult numAlloc σ
  let varStorePost := [varStore, cmd.getHashConsState numAlloc σ, numAlloc|cmd.getCircuit numAlloc σ]ₑ.varStore
  let σPost := cmd.getHashConsState numAlloc σ
  toIdeal varStorePost σPost result = .some spec ∧
  cmd.wellFormed numAlloc varStore σ

namespace eq

opaque spec {p} (a b : ZMod p) : Bool :=
  a == b

opaque Convert.toIdeal (varStore : VarStore p) (σ : HashConsSt p) (result : FB) : Option Bool

/--
Aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
@[simp, grind =]
lemma getCircuit_liftM {α} {action : HashConsM p α} {numAlloc} {σ : HashConsSt p} :
  (liftM (m := HashConsM p) (n := ClapM p) action).getCircuit numAlloc σ = #[] := by
  rfl

/--
AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
-/
@[simp, grind =]
lemma getCircuit_isZero {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (isZero e!).getCircuit numAlloc σ = #[.isZero e!] := by
  simp [isZero]

@[simp, grind =]
lemma getCircuit_eq0 {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (eq0 e!).getCircuit numAlloc σ = #[.eq0 e!] := by
  simp [eq0]

@[simp, grind =]
lemma getCircuit_share {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (share e!).getCircuit numAlloc σ = #[.share e!] := by
  simp [share]

@[simp, grind =]
lemma getCircuit_num2bits {w : ℕ} {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (num2bits w e!).getCircuit numAlloc σ = #[.num2bits w e!] := by
  simp [num2bits]

def _root_.Clap.HashConsM.getResult {α} (action : HashConsM p α) (σ : HashConsSt p) : α :=
  (action.run σ).1

/--
Waaaaaaaaaagh!
-/
@[simp, grind =]
lemma getResult_liftM {α} {action : HashConsM p α} {numAlloc} {σ : HashConsSt p} :
  (liftM (m := HashConsM p) (n := ClapM p) action).getResult numAlloc σ = action.getResult σ := by
  rfl

@[simp, grind =]
lemma getHashConsState_isZero {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (isZero e!).getHashConsState numAlloc σ =
  if .v numAlloc ∈ σ.exprs
  then σ
  else σ.pushExpr (.v numAlloc) (by simp) := by
  grind [isZero]

@[simp, grind =]
lemma getNumAlloc_liftM {α} {action : HashConsM p α} {numAlloc} {σ : HashConsSt p} :
  (liftM (m := HashConsM p) (n := ClapM p) action).getNumAlloc numAlloc σ = numAlloc := rfl
  

lemma matches_spec
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (a b : F)
  (a_val b_val : ZMod p)
  (h_a_wf_σ : a < σ.size)
  (h_b_wf_σ : b < σ.size)
  (h_a_wf : [varStore|Expr.mk a σ].isSome = true)
  (h_a_val : [varStore,σ|a].get h_a_wf = a_val)
  (h_b_wf : [varStore|Expr.mk b σ].isSome = true)
  (h_b_val : [varStore,σ|b].get h_b_wf = b_val)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    Convert.toIdeal
    (eq a b)
    (spec a_val b_val)
:= by
  dsimp [F.matches_spec]
  set aExpr : Expr _ := ⟨a, σ⟩
  set bExpr : Expr _ := ⟨b, σ⟩
  have : aExpr.wellFormed := by grind
  have : bExpr.wellFormed := by grind
  set f := a.eq b (p := p) with hf
  have : f.getCircuit numAlloc σ = #[Gate.isZero ((HashConsM.mkSub a b).getResult σ)] := by
    simp [hf, eq]
  have : f.getHashConsState numAlloc σ = σ := by
    rw [hf]
    unfold eq
    rw [ClapM.getHashConsState_bind]
    simp
      

    done
  
  
  


  sorry

end eq

namespace oneHotRaw

opaque spec (len : ℕ) (idx : ℕ) : Vector Bool len :=
  (Vector.range len).map (fun (i:ℕ) ↦ idx == i)

opaque Convert.toIdeal {len : ℕ} (varStore : VarStore p) (σ : HashConsSt p) (result : Vector FB len) : Option (Vector Bool len)


--TODO prove using eq.matches_spec
--this may require adding to F.matches_spec, or defining properties about Convert.toIdeal
--in either case, the goal is to reach a fixed point where the same properties are known about the two Convert.toIdeal functions,
--and the same F.matches_spec is being used for eq and proven for oneHotRaw
lemma matches_spec
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {idx_val : ℕ}
  (h_idx_wf : [varStore|Expr.mk idx σ].isSome = true)
  (h_idx_val : ([varStore,σ|idx].get h_idx_wf).val = idx_val)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    Convert.toIdeal
    (oneHotRaw len idx)
    (spec len idx_val)
:= by
  done

end oneHotRaw

end F

end Clap.Lang
