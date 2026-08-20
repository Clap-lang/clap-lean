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
  let varStorePost := cmd.getVarStore varStore numAlloc σ
  let σPost := cmd.getHashConsState numAlloc σ
  toIdeal varStorePost σPost result = .some spec ∧
  cmd.wellFormed numAlloc varStore σ

opaque F.Convert.toIdeal (varStore : VarStore p) (σ : HashConsSt p) (result : F) : Option (ZMod p)
opaque FB.Convert.toIdeal (varStore : VarStore p) (σ : HashConsSt p) (result : FB) : Option Bool

namespace eq

opaque spec {p} (a b : ZMod p) : Bool :=
  a == b

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

@[simp, grind .]
lemma wellFormed_pure {α} {action : α} {numAlloc} {varStore : VarStore p} {σ : HashConsSt p}:
  (pure (f := ClapM p) action).wellFormed numAlloc varStore σ := by
  grind

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
    FB.Convert.toIdeal
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
    sorry

    done





  sorry

end eq

namespace oneHotRaw

def spec (len : ℕ) (idx : ℕ) : Vector Bool len :=
  (Vector.range len).map (fun (i:ℕ) ↦ idx == i)

opaque Convert.toIdeal {len : ℕ} (varStore : VarStore p) (σ : HashConsSt p) (result : Vector FB len) : Option (Vector Bool len)


-- lemma Vector.mapM_append {p} {α β} {n} {n'}
--     {f : α → ClapM p β} {xs : Vector α n} :
--     xs.mapM f =
--     (λ numAlloc σ => (((), ), ))
-- := by
--   done

@[simp, grind =]
lemma _root_.Clap.ClapM.Vector.mapM_singleton
  {α}
  {len : α}
  (f : α → ClapM p FB)
:
  #v[len].mapM f =
  f len >>= fun x => pure #v[x]
:= by
  unfold Vector.mapM
  cbv
  simp [WriterT.run]
  funext
  simp [StateT.bind]
  cbv

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
  -- (h : (Expr.mk idx σ).wellFormed)
  -- (h_idx_wf : [varStore, σ|idx].isSome = true)
  -- (h_idx_val : ([varStore,σ|idx].get h_idx_wf).val = idx_val)
  (h_idx_val : F.Convert.toIdeal varStore σ idx = .some idx_val)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    Convert.toIdeal
    (oneHotRaw len idx)
    (spec len idx_val)
:= by
  unfold F.matches_spec
  dsimp
  set f := oneHotRaw len idx (p := p) with eq
  unfold oneHotRaw at eq
  set range_vec := Vector.range len
  induction' len with len ih
  · have : Vector.range 0 = #v[] := rfl
    simp [this, range_vec] at eq
    subst f
    simp [eq]
    unfold spec
    simp [this]
    have todoLater₁ : Convert.toIdeal varStore σ #v[] = some #v[] := sorry
    exact todoLater₁
  · simp at ih
    specialize ih (by rfl)
    have :
      oneHotRaw (len + 1) idx =
      do
        let vec ← oneHotRaw len idx
        let idx_val ← liftM (HashConsM.mkConstant (p := p) len)
        let elem ← F.eq (p := p) idx idx_val
        return vec.push elem
    := by
      simp [oneHotRaw, Vector.range_succ, Vector.mapM_append, -Vector.append_singleton]
      set v := Vector.mapM
          (fun i => do
            let idx_val ← liftM (HashConsM.mkConstant (i : ZMod p))
            idx.eq (p := p) idx_val)
          (Vector.range len)
      simp
    unfold oneHotRaw at this
    simp [range_vec, this] at eq
    rewrite [←oneHotRaw.eq_def] at eq
    apply And.intro
    . have : spec (len + 1) idx_val = spec len idx_val ++ #v[idx_val == len] := by
        unfold spec
        simp [Vector.range_succ]
      rw [this]
      have :
        Convert.toIdeal
          (f.getVarStore varStore numAlloc σ)
          (f.getHashConsState numAlloc σ)
          (f.getResult numAlloc σ) =
        (Convert.toIdeal
          ((oneHotRaw len idx).getVarStore varStore numAlloc σ)
          ((oneHotRaw len idx).getHashConsState numAlloc σ)
          ((oneHotRaw len idx).getResult numAlloc σ)).get (by grind) ++
        #v[(F.Convert.toIdeal
            ((oneHotRaw len idx).getVarStore varStore numAlloc σ)
            ((oneHotRaw len idx).getHashConsState numAlloc σ)
            idx).map (ZMod.val) == .some len
        ]
      := by
        done
      simp [this, ih, h_idx_val]
      congr 1
      done
    . simp [eq]
      apply ClapM.bind_wellFormed (by grind)
      apply ClapM.bind_wellFormed
      . grind
      . simp [map_eq_pure_bind, -bind_pure_comp]
        apply ClapM.bind_wellFormed
        . have := @F.eq.matches_spec p _
            [varStore, (oneHotRaw len idx).getHashConsState numAlloc σ, numAlloc|(oneHotRaw len idx).getCircuit numAlloc σ]ₑ.varStore
            ((oneHotRaw len idx).getNumAlloc numAlloc σ)
            ((liftM (n := ClapM p) (HashConsM.mkConstant (len : ZMod p))).getHashConsState ((oneHotRaw len idx).getNumAlloc numAlloc σ) ((oneHotRaw len idx).getHashConsState numAlloc σ))
            idx
            ((HashConsM.mkConstant ↑len).getResult ((oneHotRaw len idx).getHashConsState numAlloc σ))
            0 0
            sorry
            sorry
            sorry
            sorry
            sorry
            sorry
          obtain ⟨_, it⟩ := this
          exact it
        . grind




  done

end oneHotRaw

end F

end Clap.Lang
