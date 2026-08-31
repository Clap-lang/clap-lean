import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert

import Clap.Lang.Wheels

namespace Clap.Lang

variable {p : ℕ}

abbrev F := ExprRef
abbrev FB := F
abbrev FArray (k) := Vector FB k

section OneHotRaw

open HashConsM

variable {p : ℕ} [p.AtLeastTwo] {start len : ℕ} {idx : F} {numAlloc : ℕ} {σ : HashConsSt p}

def eq {p : ℕ} [p.AtLeastTwo] (a b : F) : ClapM p FB := do
  isZero (←mkSub (p := p) a b)

def oneHotRaw_aux (start len : ℕ) (idx : F) : ClapM p (Vector FB len) :=
  (Vector.range' start len).mapM (fun (i:ℕ) ↦ do
    let idx_val ← mkConstant (p := p) i
    eq idx idx_val
  )

/--
Why is this missing...
-/
@[simp, grind =]
lemma _root_.Vector.mapM_cast {m : Type → Type} [Monad m] [LawfulMonad m]
  {α β : Type} {n k : Nat} {h : n = k}
  {f : α → m β}
  {v : Vector α n} :
  (v.cast h).mapM f = (fun v : Vector β n ↦ v.cast h) <$> (v.mapM f) := by
  subst h
  simp

/--
Yeah ok...
-/
@[simp, grind =]
lemma _root_.Vector.mapM_singleton {m : Type → Type} [Monad m] [LawfulMonad m]
  {α β : Type}
  {f : α → m β} {x} :
  #v[x].mapM f = f x >>= (pure #v[·]) := by
  rw [←map_inj_right (f := Vector.toArray) (by aesop)]
  simp

@[simp, grind =]
lemma oneHotRaw_aux_zero :
  oneHotRaw_aux (p := p) start 0 idx = pure #v[] := by
  conv_lhs => unfold oneHotRaw_aux
  rw [show Vector.range' start 0 = #v[] from rfl]
  simp

@[simp, grind =]
lemma oneHotRaw_aux_succ :
  oneHotRaw_aux start (len + 1) idx =
  do
    let idx_val ← liftM (mkConstant (p := p) start)
    let eq ← eq (p := p) idx idx_val
    return Vector.cast (show 1 + len = len + 1 by grind)
                       (#v[eq] ++ (←oneHotRaw_aux (start + 1) len idx)) := by
  conv_lhs => unfold oneHotRaw_aux
  rw [Vector.range'_succ]
  rw [Vector.mapM_cast]
  rw [Vector.mapM_append]
  conv_lhs => simp
  rw [←oneHotRaw_aux.eq_def]
  simp

def oneHotRaw (len : ℕ) (idx : F) : ClapM p (Vector FB len) :=
  oneHotRaw_aux 0 len idx

def oneHotRaw'_aux (start len : ℕ) (idx : F) : ClapM p (List FB) :=
  (List.range' start len).mapM (fun (i : ℕ) ↦ do
    let idx_val ← mkConstant (p := p) i
    eq idx idx_val
  )

@[simp, grind =]
lemma oneHotRaw'_aux_zero :
  oneHotRaw'_aux (p := p) start 0 idx = pure [] := by
  conv_lhs => unfold oneHotRaw'_aux
  simp

@[simp, grind =]
lemma oneHotRaw'_aux_succ :
  oneHotRaw'_aux start (len + 1) idx =
  do
    let idx_val ← liftM (mkConstant (p := p) start)
    let eq ← eq (p := p) idx idx_val
    return (eq :: (←oneHotRaw'_aux (start + 1) len idx)) := by
  conv_lhs => unfold oneHotRaw'_aux
  rw [List.range'_succ]
  rw [List.mapM_cons]
  rw [←oneHotRaw'_aux.eq_def]
  simp

def oneHotRaw' (len : ℕ) (idx : F) : ClapM p (List FB) := oneHotRaw'_aux 0 len idx

@[simp, grind =]
lemma oneHotRaw'_zero :
  oneHotRaw' (p := p) 0 idx = pure [] := by
  simp [oneHotRaw']

@[simp, grind =]
lemma oneHotRaw'_succ :
  oneHotRaw' (len + 1) idx =
  do
    let idx_val ← liftM (mkConstant (p := p) 0)
    let eq ← eq (p := p) idx idx_val
    return (eq :: (←oneHotRaw'_aux 1 len idx)) := by
  simp [oneHotRaw']

@[simp, grind _=_]
lemma toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux :
  Vector.toList <$> (oneHotRaw_aux (p := p) start len idx) =
  oneHotRaw'_aux start len idx := by
  induction' len with len ih generalizing start
  · simp
  · rw [oneHotRaw'_aux_succ, oneHotRaw_aux_succ]
    specialize ih (start := start + 1)
    rw [←ih]
    simp
    grind

omit [p.AtLeastTwo] in
@[simp, grind _=_]
lemma getResult_toList {vecM : ClapM p (Vector FB len)} :
  ClapM.getResult (Vector.toList <$> vecM) numAlloc σ =
  (vecM.getResult numAlloc σ).toList := by
  simp

@[simp, grind _=_]
lemma toList_getResult_oneHotRaw :
  ((oneHotRaw_aux (p := p) start len idx).getResult numAlloc σ).toList =
  (oneHotRaw'_aux start len idx).getResult numAlloc σ := by
  rw [←toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux, ClapM.getResult_map]

@[simp, grind _=_]
lemma getCircuit_oneHotRaw_aux :
  (oneHotRaw_aux (p := p) start len idx).getCircuit numAlloc σ =
  (oneHotRaw'_aux start len idx).getCircuit numAlloc σ := by
  rw [←toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux, ClapM.getCircuit_map]

@[simp, grind _=_]
lemma getHashConsState_oneHotRaw_aux :
  (oneHotRaw_aux (p := p) start len idx).getHashConsState numAlloc σ =
  (oneHotRaw'_aux start len idx).getHashConsState numAlloc σ := by
  rw [←toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux, ClapM.getHashConsState_map]

@[simp, grind _=_]
lemma getNumAlloc_oneHotRaw_aux :
  (oneHotRaw_aux (p := p) start len idx).getNumAlloc numAlloc σ =
  (oneHotRaw'_aux start len idx).getNumAlloc numAlloc σ := by
  rw [←toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux, ClapM.getNumAlloc_map]

@[simp, grind _=_]
lemma toList_map_oneHotRaw_eq_oneHotRaw' :
  Vector.toList <$> (oneHotRaw (p := p) len idx) =
  oneHotRaw' len idx := toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux

end OneHotRaw

namespace F

def Converts := Clap.Converts 1 (fun x : ZMod p ↦ #v[x])
structure ConvertsM
  (action : ClapM p F)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  (val : ZMod p)
: Prop where
  result : Converts
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    #v[action.getResult numAlloc σ]
    val
  wellFormed : action.wellFormed numAlloc varStore σ

structure Spec (action : ClapM p F) (varStore) (numAlloc) (σ) where
  spec : ZMod p
  converts : ConvertsM action varStore numAlloc σ spec

end F

namespace FB

def Converts := Clap.Converts 1 (fun x : Bool ↦ #v[if x then (1 : ZMod p) else 0])
structure ConvertsM
  (action : ClapM p FB)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  (val : Bool)
: Prop where
  result : Converts
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    #v[action.getResult numAlloc σ]
    val
  wellFormed : action.wellFormed numAlloc varStore σ

lemma convertsM_of_convertsM_eq
  {action : ClapM p FB}
  {varStore numAlloc σ val₁}
  (val₂ : Bool)
  (h : ConvertsM action varStore numAlloc σ val₂)
  (h_eq : val₁ = val₂)
:
  ConvertsM action varStore numAlloc σ val₁
where
  result := by rewrite [h_eq]; exact h.result
  wellFormed := h.wellFormed

-- TODO generalise
lemma convertsM_bind
  (action : ClapM p F)
  (function : F → ClapM p FB)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {action_val : ZMod p}
  (function_val : ZMod p → Bool)
  (h_action : F.ConvertsM action varStore numAlloc σ action_val)
  (h_function : FB.ConvertsM
    (function (action.getResult numAlloc σ))
    (action.getVarStore varStore numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) varStore numAlloc σ (function_val action_val)
:= by
  constructor
  . simp
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed

structure Spec (action : ClapM p FB) (varStore) (numAlloc) (σ) where
  spec : Bool
  converts : ConvertsM action varStore numAlloc σ spec

end FB


namespace FArray

def Converts (k : ℕ) := Clap.Converts k
  fun vec : Vector Bool k ↦ vec.map fun x ↦ if x then (1 : ZMod p) else 0

def Converts' := Clap.Converts'
  fun l : List Bool ↦ l.map fun x ↦ if x then (1 : ZMod p) else 0

@[aesop unsafe apply, grind .]
lemma converts_of_converts' {k} {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
  {exprs : Vector ExprRef k} {val : Vector Bool k}
  (h : Converts' varStore σ numAlloc exprs.toList val.toList) :
  Converts k varStore σ numAlloc exprs val := by
  unfold Converts
  unfold Converts' at h
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  have : exprs.toList.length = k := by aesop
  rw! (castMode := .all) [this] at h₁ h₂ h₃ h₄
  constructor <;> intros i <;>
  · specialize_all i
    grind

structure ConvertsM {k}
  (action : ClapM p (Vector FB k))
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  (val : Vector Bool k)
: Prop where
  result : Converts k
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getResult numAlloc σ)
    val
  wellFormed : action.wellFormed numAlloc varStore σ

lemma ConvertsM.def {k numAlloc} {action : ClapM p (Vector FB k)}
                  {varStore : VarStore p} {σ : HashConsSt p} {val : Vector Bool k}:
  ConvertsM action varStore numAlloc σ val ↔
  Converts k
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getResult numAlloc σ)
    val ∧
  action.wellFormed numAlloc varStore σ := by
  apply Iff.intro <;> intros h
  rcases h
  grind
  constructor
  grind
  grind

structure ConvertsM'
  (action : ClapM p (List FB))
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  (val : List Bool)
: Prop where
  result : Converts'
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getResult numAlloc σ)
    val
  wellFormed : action.wellFormed numAlloc varStore σ

lemma ConvertsM'.def {numAlloc} {action : ClapM p (List FB)}
                     {varStore : VarStore p} {σ : HashConsSt p} {val : List Bool}
:
  ConvertsM' action varStore numAlloc σ val ↔
  Converts'
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getResult numAlloc σ)
    val ∧
  action.wellFormed numAlloc varStore σ := by
  apply Iff.intro <;> intros h
  rcases h
  grind
  constructor
  grind
  grind

@[aesop unsafe apply, grind .]
lemma convertsM_of_ConvertsM' {k numAlloc : ℕ} {varStore : VarStore p} {σ : HashConsSt p} {val : Vector Bool k}
                              {action : ClapM p (Vector FB k)}
                              (h : ConvertsM' (Vector.toList <$> action) varStore numAlloc σ val.toList) :
  ConvertsM action varStore numAlloc σ val := by
  rw [ConvertsM.def]; rw [ConvertsM'.def] at h
  grind

-- TODO generalise
lemma convertsM_bind
  {len1 len2}
  (action : ClapM p (FArray len1))
  (function : (FArray len1) → ClapM p (FArray len2))
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {action_val : Vector Bool len1}
  (function_val : Vector Bool len1 → Vector Bool len2)
  (h_action : FArray.ConvertsM action varStore numAlloc σ action_val)
  (h_function : FArray.ConvertsM
    (function (action.getResult numAlloc σ))
    (action.getVarStore varStore numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) varStore numAlloc σ (function_val action_val)
:= by
  constructor
  . simp
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed

lemma convertsM'_bind
  (action : ClapM p FB)
  (function : FB → ClapM p (List ExprRef))
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {action_val : Bool}
  (function_val : Bool → List Bool)
  (h_action : FB.ConvertsM action varStore numAlloc σ action_val)
  (h_function : FArray.ConvertsM'
    (function (action.getResult numAlloc σ))
    (action.getVarStore varStore numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (function_val action_val)
  )
:
  ConvertsM' (action >>= function) varStore numAlloc σ (function_val action_val)
:= by
  constructor
  . simp
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed

-- TODO generalize
lemma convertsM_map_FB_FArray
  {len}
  (action : ClapM p FB)
  (f : FB → Vector FB len)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {action_val : Bool}
  (f_val : Bool → Vector Bool len)
  (h_action : FB.ConvertsM action varStore numAlloc σ action_val)
  (h_f_val : FArray.Converts len
    (action.getVarStore varStore numAlloc σ)
    (action.getHashConsState numAlloc σ)
    (action.getNumAlloc numAlloc σ)
    (f (action.getResult numAlloc σ))
    (f_val action_val)
  )
:
  ConvertsM (f <$> action) varStore numAlloc σ (f_val action_val)
:= by
  constructor
  . simp
    apply h_f_val
  . rewrite [ClapM.map_wellFormed]
    apply h_action.wellFormed

-- lemma convertsM_map_FB_FArray
--   {len}
--   (action : ClapM p FB)
--   (f : FB → Vector FB len)
--   (varStore : VarStore p)
--   (numAlloc : ℕ)
--   (σ : HashConsSt p)
--   {action_val : Bool}
--   (f_val : Bool → Vector Bool len)
--   (h_action : FArray.ConvertsM action varStore numAlloc σ action_val)
--   (h_f_val : FArray.Converts len
--     (action.getVarStore varStore numAlloc σ)
--     (action.getHashConsState numAlloc σ)
--     (action.getNumAlloc numAlloc σ)
--     (f (action.getResult numAlloc σ))
--     (f_val action_val)
--   )
-- :
--   ConvertsM (f <$> action) varStore numAlloc σ (f_val action_val)
-- := by
--   constructor
--   . simp
--     apply h_f_val
--   . rewrite [ClapM.map_wellFormed]
--     apply h_action.wellFormed

@[aesop safe]
lemma convertsM_pure
        {varStore : VarStore p}
        {numAlloc : ℕ}
        {σ : HashConsSt p}
        {k : ℕ}
        {x : FArray k}
        {val : Vector Bool k}
        (h : FArray.Converts k varStore σ numAlloc x val)
  : ConvertsM (pure x) varStore numAlloc σ val := by
  constructor
  · simpa
  · grind

@[simp]
lemma converts_empty
        {varStore : VarStore p}
        {numAlloc : ℕ}
        {σ : HashConsSt p}
  : Converts 0 varStore σ numAlloc #v[] #v[] := by
  constructor
  · simp
  · grind
  · grind

@[aesop safe]
lemma convertsM'_pure
        {varStore : VarStore p}
        {numAlloc : ℕ}
        {σ : HashConsSt p}
        {x : List ExprRef}
        {val : List Bool}
        (h : FArray.Converts' varStore σ numAlloc x val)
  : ConvertsM' (pure x) varStore numAlloc σ val := by
  constructor
  · simpa
  · grind

@[simp]
lemma converts'_empty
        {varStore : VarStore p}
        {numAlloc : ℕ}
        {σ : HashConsSt p}
  : Converts' varStore σ numAlloc [] [] := by
  constructor
  . simp
  · simp
  · grind
  · grind

lemma converts_push
  {k : ℕ}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {numAlloc : ℕ}
  {exprs : Vector FB k}
  {expr : FB}
  {vals : Vector Bool k}
  {val : Bool}
  (h_exprs : FArray.Converts k varStore σ numAlloc exprs vals)
  (h_expr : FB.Converts varStore σ numAlloc #v[expr] val)
:
  FArray.Converts (k + 1) varStore σ numAlloc (exprs.push expr) (vals.push val)
:= by
  obtain ⟨exprs_varSet, exprs_wellFormed, exprs_result⟩ := h_exprs
  obtain ⟨expr_varSet, expr_wellFormed, expr_result⟩ := h_expr
  simp at *
  constructor
  all_goals {
    intro i
    simp
    rewrite [Vector.getElem_push]
    split
    . specialize_all ⟨i.val, by assumption⟩
      grind
    . grind
  }

end FArray

@[grind =]
lemma deref_idxOf_of_mem
  {cacheExpr : CacheExpr p}
  {σ : HashConsSt p}
  (h_mem : cacheExpr ∈ σ.exprs)
:
  *⦃σ.exprs.idxOf cacheExpr, σ⦄ = cacheExpr
:= by
  grind

@[simp, grind =]
lemma deref_mkVar_eq_some
  {idx : ℕ}
  {σ : HashConsSt p}
:
  *⦃(HashConsM.mkVar idx).getResult σ, (HashConsM.mkVar idx).getHashConsState σ⦄ =
  .some (CacheExpr.v idx)
:= by
  grind [=HashConsM.mkVar]

@[simp, grind =]
lemma varSet_mkVar
  {idx : ℕ}
  {σ : HashConsSt p}
:
  ⦃(HashConsM.mkVar idx).getResult σ, (HashConsM.mkVar idx).getHashConsState σ⦄.varSet =
  {idx}
:= by
  unfold Expr.varSet
  grind

@[simp, grind! .]
lemma lt_getNumAlloc_isZero
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : ExprRef}
:
  numAlloc < (isZero a).getNumAlloc numAlloc σ
:= by
  simp [isZero]

namespace isZero

lemma wellFormed {e! : ExprRef} {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ} {value : ZMod p}
  (h : F.Converts Γ σ numAlloc #v[e!] value)
:
  (isZero e!).wellFormed numAlloc Γ σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_isZero
  . grind
  . have : [Γ|⦃e!, σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : F}
  {a_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
:
  FB.Converts
    ((isZero a).getVarStore varStore numAlloc σ)
    ((isZero a).getHashConsState numAlloc σ)
    ((isZero a).getNumAlloc numAlloc σ)
    #v[(isZero a).getResult numAlloc σ]
    (a_val == 0)
:= by
  obtain ⟨a_varSet, a_wellFormed, a_result⟩ := h_a
  constructor <;> simp at *
  . intro i h_i
    grind [=isZero]
  . simp [isZero]
    rw [Expr.wellFormed_iff_isSome, deref_mkVar_eq_some]
    rfl
  . simp [isZero, HashConsM.mkVar]
    simp [HashConsM.getHashConsState_saveExpr_of_wellFormed,
          HashConsM.getResult_saveExpr_of_wellFormed]
    split
    · rw [eval_eq_evalRec (by grind)]
      unfold Expr.evalRec
      grind
    · rw [eval_eq_evalRec (by grind)]
      rw [evalRec_eq_of_deref_eq_some_v (idx := numAlloc)]
      · simp
        rw [eval_eq_evalRec (by grind)] at a_result ⊢
        rw [←evalRec_of_wellFormed_of_prefix] at ⊢
        · rw [a_result]
          grind
        · grind
        · grind
      · grind

lemma convertsM
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : F}
  {a_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
:
  FB.ConvertsM (isZero a)
    varStore
    numAlloc
    σ
    (a_val == 0)
where
  result := converts h_a
  wellFormed := wellFormed h_a

def spec [p.AtLeastTwo]
  {a : F} {varStore : VarStore p} {numAlloc} {σ} {a_val}
  (h: (F.Converts varStore σ numAlloc #v[a] a_val))
:
  FB.Spec (isZero a) varStore numAlloc σ
where
  spec := a_val == 0
  converts := convertsM h

end isZero


namespace mkSub

lemma converts
   {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : F.Converts Γ σ numAlloc #v[a] a_val)
   (h_b : F.Converts Γ σ numAlloc #v[b] b_val)
:
  F.Converts
    (ClapM.getVarStore (liftM (HashConsM.mkSub (p := p) a b)) Γ numAlloc σ)
    (ClapM.getHashConsState (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ)
    (ClapM.getNumAlloc (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ)
    #v[ClapM.getResult (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ]
    (a_val - b_val)
:= by
  simp
  obtain ⟨a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . simp [HashConsM.mkSub]
    rewrite [HashConsM.getResult_saveExpr_of_wellFormed]
    . rewrite [HashConsM.getHashConsState_saveExpr_of_wellFormed (by grind)]
      . split <;> rewrite [eval_eq_evalRec (by grind)]
        . rewrite [evalRec_eq_of_deref_eq_some_sub (deref_idxOf_of_mem (by assumption))]
          dsimp
          rewrite [
            ←eval_eq_evalRec (by grind),
            ←eval_eq_evalRec (by grind),
            a_result,
            b_result
          ]
          rfl
        . rewrite [evalRec_eq_of_deref_eq_some_sub (Expr.deref_mk_size_push)]
          dsimp
          rewrite [
            ←evalRec_of_wellFormed_of_prefix (σ := σ) (by grind) (by grind),
            ←evalRec_of_wellFormed_of_prefix (σ := σ) (σ' := HashConsSt.pushExpr _ _ _) (by grind) (by grind),
            ←eval_eq_evalRec (by grind),
            ←eval_eq_evalRec (by grind),
            a_result,
            b_result
          ]
          rfl
    . grind

lemma convertsM
  {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
  {a b : ExprRef}
  {a_val b_val : ZMod p}
  (h_a : F.Converts Γ σ numAlloc #v[a] a_val)
  (h_b : F.Converts Γ σ numAlloc #v[b] b_val)
:
  F.ConvertsM (liftM (HashConsM.mkSub (p := p) a b)) Γ numAlloc σ (a_val - b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkSub

def spec
  {a b : F} {varStore : VarStore p} {numAlloc} {σ} {a_val b_val}
  (h_a: (F.Converts varStore σ numAlloc #v[a] a_val))
  (h_b: (F.Converts varStore σ numAlloc #v[b] b_val))
:
  F.Spec (liftM (HashConsM.mkSub (p := p) a b)) varStore numAlloc σ
where
  spec := a_val - b_val
  converts := convertsM h_a h_b

end mkSub

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a b : F}
  {a_val b_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
  (h_b : F.Converts varStore σ numAlloc #v[b] b_val)
:
  FB.ConvertsM (eq a b) varStore numAlloc σ (a_val == b_val)
:= by
  unfold eq
  apply FB.convertsM_of_convertsM_eq (a_val- b_val == 0)
  . exact FB.convertsM_bind _ _ _ _ _ (λ x => x == (0 : ZMod p))
      (mkSub.convertsM h_a h_b)
      (isZero.convertsM (mkSub.convertsM h_a h_b).result)
  . grind

-- def spec [p.AtLeastTwo]
--   {a b : F} {varStore : VarStore p} {numAlloc} {σ} {a_val} {b_val}
--   (h : (F.Converts varStore σ numAlloc #v[a] a_val))
--   (h : (F.Converts varStore σ numAlloc #v[b] b_val))
-- :
--   FB.Spec (eq a b) varStore numAlloc σ
-- where
--   spec := a_val == b_val
--   converts := by
--     unfold eq
--     --

lemma convertsM'
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a b : F}
  {a_val b_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
  (h_b : F.Converts varStore σ numAlloc #v[b] b_val)
:
  FB.ConvertsM (eq a b) varStore numAlloc σ (a_val == b_val)
:= by
  unfold eq
  apply FB.convertsM_of_convertsM_eq (a_val- b_val == 0)
  . exact FB.convertsM_bind _ _ _ _ _ (λ x => x == (0 : ZMod p))
      (mkSub.convertsM h_a h_b)
      (isZero.convertsM (mkSub.convertsM h_a h_b).result)
  . grind

end eq

namespace MkConstant

@[simp]
lemma convertsM
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {x : ZMod p} :
  F.ConvertsM (liftM (HashConsM.mkConstant (p := p) x)) varStore numAlloc σ x := by
  constructor
  · simp
    simp_rw [HashConsM.getResult_mkConstant, HashConsM.getHashConsState_mkConstant]
    unfold F.Converts
    constructor <;> simp
    · grind [=Expr.varSet, =Expr.varSet_wellFormed]
    · grind
    · rw [eval_eq_evalRec (by grind)]
      grind
  · grind

end MkConstant

/--
This one for any `LawfulMonad` sure was fun.
-/
@[simp, grind =]
lemma _root_.Vector.mapM_singleton'
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

namespace MapM

lemma _root_.Vector.take_append_last
  {α}
  {len : ℕ}
  {vec : Vector α (len + 1)}
:
  ((vec.take len).cast (m := len) (by grind)) ++ #v[vec[len]] =
  vec
:= by
  simp
  ext
  expose_names
  have := Vector.getElem_append (n := len) (m := 1) (ys := #v[vec[len]]) (xs := vec.pop) (i := i) (by grind)
  rewrite [this]
  aesop (add safe (by grind))

lemma _root_.Vector.mapM_succ
  {α}
  {len : ℕ}
  {vec : Vector α (len + 1)}
  (f : α → ClapM p FB)
:
  vec.mapM f =
  (vec.pop.mapM f) >>= λ v => (λ x => v.push x) <$> f vec[len]
:= by
  rewrite [←Vector.take_append_last (vec:=vec)]
  rw [Vector.mapM_append]
  simp
  have := Vector.take_append_last (vec:=vec)
  simp at this
  congr
  . exact this.symm
  . funext vecM
    congr
    exact this.symm

-- @[simp]
-- lemma convertsM
--   {varStore : VarStore p}
--   {numAlloc : ℕ}
--   {σ : HashConsSt p}
--   {α : Type}
--   {f : α → ClapM p FB}
--   {k : ℕ}
--   {xs : Vector α k}
--   {vars : Vector Bool k}
--   (h : ∀ varStore numAlloc (σ : HashConsSt p),
--     ∀ (i : Fin k), FB.ConvertsM (f xs[i]) varStore numAlloc σ vars[i]) :
--   FArray.ConvertsM (xs.mapM f) varStore numAlloc σ vars := by
--   induction' k with k ih
--   · have eq₁ : xs = #v[] := by grind
--     have eq₂ : vars = #v[] := by grind
--     subst eq₁ eq₂
--     simp [FArray.convertsM_pure]
--   . rewrite [Vector.mapM_succ]
--     have h' : ∀ (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p) (i : Fin k),
--       FB.ConvertsM (f xs.pop[i]) varStore numAlloc σ vars.pop[i]
--     := by
--       intro varStore numAlloc σ i
--       rewrite [
--         show xs.pop[i] = xs[i] by grind,
--         show vars.pop[i] = vars[i] by grind,
--       ]
--       exact h varStore numAlloc σ ⟨i, by grind⟩
--     have h_action := @ih xs.pop vars.pop h'
--     have h_bind := @FArray.convertsM_bind
--       p k (k + 1)
--       (action := Vector.mapM f xs.pop)
--       (function := λ v => (λ x => v.push x ) <$> f xs[k])
--       varStore numAlloc σ
--       (action_val := vars.pop)
--       (function_val := λ v => v.push vars[k])
--       h_action
--     have h_k_plus_one : (vars.pop.push vars[k]).cast (m := k + 1) (by grind) = vars := by
--       simp
--       ext
--       rewrite [Vector.getElem_push]
--       split
--       . obtain ⟨⟨l⟩, h_l⟩ := vars
--         simp
--       . congr
--         grind
--     simp at h_k_plus_one
--     rewrite [h_k_plus_one] at h_bind
--     apply h_bind
--     have h_map := @FArray.convertsM_map_FB_FArray p (k + 1)
--       (action := f xs[k])
--       (f := (fun x => Vector.push ((Vector.mapM f xs.pop).getResult numAlloc σ) x))
--       ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--       ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--       ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--       (action_val := vars[k])
--       (λ x => vars.pop.push x)
--       (h
--         ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--         ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--         ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--         ⟨k, Nat.lt_succ_self k⟩
--       )
--     have h_k_plus_one_minus_one_plus_one : vars.pop.push vars[k] = vars := by
--       simp
--       ext
--       rewrite [Vector.getElem_push]
--       split
--       . obtain ⟨⟨l⟩, h_l⟩ := vars
--         simp
--       . congr
--         grind
--     rewrite [h_k_plus_one_minus_one_plus_one] at h_map
--     convert h_map _
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . rfl
--     . have := @FArray.converts_push p k
--         (varStore := ((f xs[k]).getVarStore ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--           ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ) ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)))
--         (σ := ((f xs[k]).getHashConsState ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--           ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)))
--         (numAlloc := ((f xs[k]).getNumAlloc ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--           ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)))
--         (exprs := (xs.pop.mapM f).getResult numAlloc σ)
--         (expr := (f xs[k]).getResult ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--           ((Vector.mapM f xs.pop).getHashConsState numAlloc σ))
--         (vals := vars.pop)
--         (val := vars[k])
--       rewrite [h_k_plus_one] at this
--       apply this
--       . clear this
--         -- apply toIdeal_run_of_toIdeal to remove f
--         -- specialize ih
--         -- consider weakening the forall varstore thing
--         done
--       . clear this
--         simp at h
--         have := h
--           ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--           ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--           ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--           ⟨k, Nat.lt_succ_self k⟩
--         simp at this
--         have := this.result
--         exact this


--         done
--       done


--     -- . specialize h
--     --     ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--     --     ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--     --     ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--     --     ⟨k, by grind⟩
--     --   exact h
--     -- . set mapM_numAlloc := ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--     --   set mapM_σ := ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--     --   set mapM_varStore := ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--     --   set mapM_result := ((Vector.mapM f xs.pop).getResult numAlloc σ)
--     --   set final_varStore := ((f xs[k]).getVarStore mapM_varStore mapM_numAlloc mapM_σ)
--     --   set final_σ := ((f xs[k]).getHashConsState mapM_numAlloc mapM_σ)
--     --   set final_numAlloc := ((f xs[k]).getNumAlloc mapM_numAlloc mapM_σ)
--     --   change
--     --     FArray.Converts (k + 1)
--     --       final_varStore
--     --       final_σ
--     --       final_numAlloc
--     --       (mapM_result.push ((f xs[k]).getResult mapM_numAlloc mapM_σ))
--     --       (vars.pop.push vars[k])
--     --   constructor
--     --   . intro i
--     --     have := @Vector.getElem_push FB (k + 1 - 1) mapM_result ((f xs[k]).getResult mapM_numAlloc mapM_σ) i (by grind)
--     --     simp [Expr.varSet_wellFormed]
--     --     intro x h_x
--     --     rw! [this] at h_x
--     --     by_cases h_i: i = k
--     --     . suffices ⦃((f xs[k]).getResult mapM_numAlloc mapM_σ), final_σ⦄.varSet_wellFormed final_numAlloc from by {

--     --       }

--     --       done
--     --     simp [Vector.getElem_push (xs := mapM_result) (i := i.val) (x := ((f xs[k]).getResult mapM_numAlloc mapM_σ))]
--     --     done
--     --   . simp
--     --     done
--     --   . simp
--     --     done

--     --   done


--   --     done







--   --   have : xs = (((xs.take k).cast (m := k) (by grind)) ++ #v[xs[k]]) := by
--   --     sorry
--   --   rw [this]
--   --   specialize @ih ((xs.take k).cast (m := k) (by grind))
--   --   rw [Vector.mapM_append]
--   --   simp at ih ⊢
--   --   convert FArray.convertsM_bind
--   --     (action := (Vector.mapM f xs.pop))
--   --     (function := λ x => (x ++ ·) <$> Vector.mapM f #v[xs[k]])
--   --     varStore numAlloc σ
--   --     (function_val := λ xs => xs.push vars[k])
--   --     (ih ?x)
--   --     ?y
--   --   . omega
--   --   . omega
--   --   . omega
--   --   . grind
--   --   . done
--   --   case succ =>
--   --     exact (vars.take k).cast (m := k) (by grind)
--   --   . obtain ⟨⟨l⟩, h_l⟩ := vars
--   --     simp
--   --     simp at h_l
--   --     rw! (occs := [1]) [←List.dropLast_append_getLast (l := l)]
--   --     congr
--   --     grind
--   --     grind
--   --   . intro varStore numAlloc σ i
--   --     specialize h varStore numAlloc σ ⟨i.val, (by grind)⟩
--   --     simp at h
--   --     simp
--   --     exact h
--   --   simp
--   --   convert FArray.convertsM_map_FB_FArray
--   --     (action := f xs[k])
--   --     (f := (fun a => (Vector.mapM f xs.pop).getResult numAlloc σ ++ #v[a]))
--   --     ((Vector.mapM f xs.pop).getVarStore varStore numAlloc σ)
--   --     ((Vector.mapM f xs.pop).getNumAlloc numAlloc σ)
--   --     ((Vector.mapM f xs.pop).getHashConsState numAlloc σ)
--   --     (f_val := λ x => vars.pop.push x)
--   --   apply Iff.intro
--   --   . intro h1 h2 h3
--   --     exact h1
--   --   . intro h1
--   --     apply h1
--   --     convert h _ _ _ ⟨k, Nat.lt_succ_self k⟩
--   --     . simp
--   --     . simp
--   --     . simp
--   --       unfold FArray.Converts
--   --       set action := f xs[k]
--   --       set base_varStore := (_ : ClapM p (Vector FB k)).getVarStore varStore numAlloc σ with eq_v
--   --       set base_numAlloc := (_ : ClapM p (Vector FB k)).getNumAlloc numAlloc σ with eq_n
--   --       set base_σ := (_ : ClapM p (Vector FB k)).getHashConsState numAlloc σ with eq_σ
--   --       rw! [←eq_n]
--   --       rw! [←eq_σ]
--   --       apply toIdeal_run_of_toIdeal
--   --       done
--   --     done
--   --   done


--   -- · sorry
--   --   simp
--   --   simp_rw [HashConsM.getResult_mkConstant, HashConsM.getHashConsState_mkConstant]
--   --   unfold F.Converts
--   --   constructor <;> simp
--   --   · grind [=Expr.varSet, =Expr.varSet_wellFormed]
--   --   · grind
--   --   · rw [eval_eq_evalRec (by grind)]
--   --     grind
--   -- · grind

end MapM

namespace oneHotRaw

lemma convertsM_but_sane?
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {len : ℕ}
  {idx : F}
  {idx_val : ZMod p} -- TODO : Fin len?
  (h_idx : F.Converts varStore σ numAlloc #v[idx] idx_val)
  (h_len : len < p)
:
  FArray.ConvertsM (oneHotRaw len idx) varStore numAlloc σ (Vector.ofFn (λ x => x.val == idx_val.val))
:= by
  apply FArray.convertsM_of_ConvertsM'
  simp_rw [toList_map_oneHotRaw_eq_oneHotRaw']
  unfold oneHotRaw' oneHotRaw'_aux

  simp [
    Vector.toList_ofFn,
    List.ofFn_eq_map,
    List.finRange_eq_pmap_range,
    List.map_pmap,
    List.range_eq_range'
  ]

  set list := List.range' 0 len
  have : ∀ x ∈ list, x < p := by grind
  -- TODO add predicate over values of list
  clear_value list

  induction' list with head tail h_tail
  . aesop
  . simp
    set mapM :=  List.mapM
          (fun i => do
            let idx_val ← liftM (HashConsM.mkConstant (i : ZMod p))
            eq (p := p) idx idx_val)
          tail
    clear_value mapM
    rewrite [←bind_assoc]
    apply FArray.convertsM'_bind
      (action_val := head == idx_val.val)
      (function_val := λ b => b :: (List.map (fun a => a == idx_val.val) tail))
    . convert FB.convertsM_bind (p := p)
        (action := (liftM (HashConsM.mkConstant (p := p) head)))
        (varStore := varStore)
        (numAlloc := numAlloc)
        (σ := σ)
        (function := eq idx)
        (action_val := head)
        (function_val := λ x => x == idx_val.val)
        MkConstant.convertsM
        ?eq
      . rewrite [←ZMod.val_cast_of_lt (a := head) (this head (by grind))]
        simp only [ZMod.val_natCast, ZMod.natCast_val, ZMod.cast_id', id_eq, beq_eq_beq]
        apply Iff.intro
        . intro h
          simp [h]
        . intro h
          simp [←h]
      . have h1 := toIdeal_run_of_toIdeal (p := p)
          (liftM (HashConsM.mkConstant (p := p) head))
          (MkConstant.convertsM.wellFormed)
          h_idx
        rewrite [←F.Converts.eq_def] at h1
        have h2 := MkConstant.convertsM (x := (head: ZMod p)) (varStore := varStore) (numAlloc := numAlloc) (σ := σ)
        have := eq.convertsM h1 h2.result
        convert this using 1
        simp
        grind
    . done
    done


  sorry -- TODO: Aaaand bob's our uncle?

-- TODO
-- this proof is bad
-- primarily because unification isn't working
-- but also because it's trying to do too much in one go
-- we should have a convertsM for each component part rather than trying to do these many steps in one go
lemma convertsM
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {len : ℕ}
  {idx : F}
  {idx_val : ZMod p} -- TODO : Fin len?
  (h_idx : F.Converts varStore σ numAlloc #v[idx] idx_val)
  (h_len : len < p)
:
  FArray.ConvertsM (oneHotRaw len idx) varStore numAlloc σ (Vector.ofFn (λ x => x.val == idx_val.val))
:= by
  unfold oneHotRaw
  induction' len with len ih
  . have this : Vector.range 0 = #v[] := by rfl
    have that : Vector.ofFn (λ (x : Fin 0) => x.val == idx_val.val) = #v[] := by rfl
    simp [this, that]
    constructor
    . constructor
      . simp
      . simp
      . simp
    . simp
  . have : Vector.range (len + 1) = (Vector.range len) ++ #v[len] := by grind
    specialize ih (by grind)
    rewrite [this, Vector.mapM_append, Vector.mapM_singleton]
    rewrite [←oneHotRaw.eq_def] at ⊢ ih
    set stepM := ((liftM (HashConsM.mkConstant (p := p) len)) >>= eq (p := p) idx)
    simp
    set stepM' := λ x => _ <$> stepM
    convert FArray.convertsM_bind ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    . rewrite [Vector.ofFn_succ]
      rfl
      -- (action := oneHotRaw len idx)
      -- (function := stepM')
      -- varStore numAlloc σ
      -- (function_val := λ x => x.push (len == idx_val.val))
      -- (h_action := ih)
    simp [Vector.ofFn_succ]; left
    unfold stepM'
    have (varStore : VarStore p) (numAlloc σ) : FB.ConvertsM stepM varStore numAlloc σ (len == idx_val) := by
      unfold stepM
      apply FB.convertsM_bind
      . sorry
      .
      done

    convert FArray.convertsM_map
      (action := stepM)
      (f := ((fun a => Vector.push ((oneHotRaw len idx).getResult numAlloc σ) a)))
      varStore numAlloc σ
      (f_val := λ b => (Vector.ofFn (λ x : Fin len => x.val == idx_val.val)).push b)


    convert FArray.convertsM_bind
      (action := oneHotRaw len idx)
      (function_val := λ v : Vector Bool len => v.push (len == idx_val))
      (varStore := varStore)
      (numAlloc := numAlloc)
      (σ := σ)
      (h_action := ih)
      (h_function := by convert FArray.convertsM_bind

      )
    . rewrite [Vector.ofFn_succ]
      aesop
      congr 1
      sorry

    rewrite [Vector.mapM_]
    done

end oneHot

#exit
#exit
#exot



  -- apply Clap.ClapM.bind_wellFormed
  -- · grind
  -- . rcases h_a with ⟨h₁, h₂, h₃⟩
  --   rcases h_b with ⟨h₄, h₅, h₆⟩
  --   simp
  --   apply wellFormed_isZero
  --   · simp at *
  --     grind
  --   · simp at *
  --     intros val hval
  --     rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
  --     -- rw [eval_eq_evalRec (by grind)] at h₃ h₆
  --     have : [varStore | ⦃a[0], σ⦄].isSome := by grind
  --     have : [varStore | ⦃b[0], σ⦄].isSome := by grind
  --     grind -- `Option.isSome_of_eq_some` is useless, had to go via `wellFormed_mem_varStore_of_evalRec_eq_some`... yikes?
  --   · simp at *
  --     grind [=Expr.varSet_wellFormed]

lemma matches_spec
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (a b : F)
  (a_val b_val : ZMod p)
  (h_a_wf_σ : (Expr.mk a σ).wellFormed)
  (h_b_wf_σ : (Expr.mk b σ).wellFormed)
  (h_a_wf : [varStore|Expr.mk a σ].isSome = true)
  (h_a_val : [varStore,σ|a].get h_a_wf = a_val)
  (h_b_wf : [varStore|Expr.mk b σ].isSome = true)
  (h_b_val : [varStore,σ|b].get h_b_wf = b_val)
  -- (h_σ_a : Expr.varSet_wellFormed ⟨a, σ⟩ numAlloc)
  -- (h_σ_b : Expr.varSet_wellFormed ⟨b, σ⟩ numAlloc)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    (eq a b)
    (a_val == b_val)
    FB.Convert.toIdeal
:= by
  dsimp [F.matches_spec]
  set aExpr : Expr _ := ⟨a, σ⟩
  have : aExpr.wellFormed := by grind

  set bExpr : Expr _ := ⟨b, σ⟩
  have : bExpr.wellFormed := by grind

  set subCExpr : CacheExpr p := .binary_op (p := p) a b .sub
  have subCExprWf : subCExpr.wellFormed σ.size := by grind

  set f := a.eq b (p := p) with hf

  have : f.getCircuit numAlloc σ = #[Gate.isZero (σ.exprs.idxOf subCExpr)] := by
    grind [eq]

  set σ₁ := (HashConsM.mkSub a b).getHashConsState σ with eq_σ₁
  have eq₁ : subCExpr ∈ σ₁.exprs := by grind
  set σ₂ := f.getHashConsState numAlloc σ with eq_σ₂
  have eq₃ : subCExpr ∈ σ₂.exprs := by grind [=eq]
  have eq₄ : .v numAlloc ∈ σ₂.exprs := by grind [=eq]
  have : f.getResult numAlloc σ = (HashConsM.mkVar numAlloc).getResult σ₁ := by
    grind [=eq]
  rw [this]
  let res₀ := (HashConsM.mkSub a b).getResult σ
  set res₁ := (HashConsM.mkVar numAlloc).getResult σ₁ with eq_res₁
  let res₀_val := [varStore| ⦃res₀, (HashConsM.mkVar numAlloc).getHashConsState σ₁⦄]
  have : f.getVarStore varStore numAlloc σ =
         varStore.insert numAlloc (if res₀_val = some 0 then 1 else 0) := by
    rw [hf]
    unfold eq
    rw [ClapM.getVarStore_bind_of_wellFormed (by simp)]
    swap
    simp
    apply wellFormed_isZero (by grind) (by grind)
    swap
    simp [res₀_val, res₀, eq_σ₁]

  sorry

end eq

namespace oneHotRaw

def spec (len : ℕ) (idx : ℕ) : Vector Bool len :=
  (Vector.range len).map (fun (i:ℕ) ↦ idx == i)

opaque Convert.toIdeal {len : ℕ} (varStore : VarStore p) (σ : HashConsSt p) (result : Vector FB len) : Option (Vector Bool len)

lemma Convert.toIdeal_push
  {len : ℕ} {vec : Vector Bool len} {extra : FB} {val : Bool}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {result : Vector FB len}
  (h_base : Convert.toIdeal varStore σ result = .some vec)
  (h_extra : FB.Convert.toIdeal varStore σ extra = .some val)
:
  Convert.toIdeal varStore σ (result.push extra) = .some (vec.push val)
:= by
  done

-- lemma Vector.mapM_append {p} {α β} {n} {n'}
--     {f : α → ClapM p β} {xs : Vector α n} :
--     xs.mapM f =
--     (λ numAlloc σ => (((), ), ))
-- := by
--   done

@[grind .]
lemma getVarStore_precedes_of_wellFormed
  {α}
  {Γ : VarStore p}
  {numAlloc : ℕ}
  {σ σ': HashConsSt p}
  {action : ClapM p α}
:
  [σ'|Γ ⊑ action.getVarStore Γ numAlloc σ]
:= by
  unfold ClapM.getVarStore
  grind

lemma wellFormed
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {idx_val : ℕ}
  (h_idx_val : (F.Convert.toIdeal varStore σ idx).map ZMod.val = .some idx_val)
  (h_idx_varSet : Expr.varSet_wellFormed ⟨idx, σ⟩ numAlloc)
:
  (oneHotRaw len idx).wellFormed numAlloc varStore σ
:= by
  have h_isSome : (F.Convert.toIdeal varStore σ idx).isSome = true := by grind
  induction' len with len h_len
  . have : Vector.range 0 = #v[] := rfl
    simp [oneHotRaw, this]
  . have :
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
    simp [this]
    apply ClapM.bind_wellFormed (by grind)
    apply ClapM.bind_wellFormed
    . grind
    . apply eq.wellFormed <;> simp
      . have h_lt: idx < σ.size := by grind [wellFormed_of_toIdeal_isSome]
        have h_le : σ.size ≤ ((oneHotRaw len idx).getHashConsState numAlloc σ).size := by grind
        apply lt_of_lt_of_le (lt_of_lt_of_le h_lt h_le)
        rewrite [HashConsM.getHashConsState_mkConstant]
        grind
      . grind [HashConsM.getResult_lt_getHashConsState_size_mkConstant] -- grind why
      . rewrite [←ClapM.getVarStore]
        have := isSome_eval_of_isSome_toIdeal h_isSome
        apply isSome_eval_of_isSome_eval_precedes (Γ₁ := varStore)
        . apply isSome_eval_of_prefix _ this
          . grind
          . grind
          . exact wellFormed_of_toIdeal_isSome h_isSome
        . have := wellFormed_of_toIdeal_isSome h_isSome
          grind
        . simp
          grind
      . unfold Expr.varSet_wellFormed
        rewrite [varSet.varSet_mk_eq_of_prefix (σ1 := σ)]
        . grind
        . grind [wellFormed_of_toIdeal_isSome]
        . apply Array.isPrefixOf_trans h_len.2.2
          apply HashConsM.wellFormed_mkConstant
      . grind [Expr.varSet_wellFormed]

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
  (h_idx_val : F.Convert.toIdeal varStore σ idx idx_val)
  (h_idx_varSet : Expr.varSet_wellFormed ⟨idx, σ⟩ numAlloc)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    (oneHotRaw len idx)
    (spec len idx_val)
    Convert.toIdeal
:= by
  unfold F.matches_spec
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
    have : spec (len + 1) idx_val = spec len idx_val ++ #v[idx_val == len] := by
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
      simp [ih]
      have :
        f.getResult numAlloc σ =
        ((oneHotRaw len idx).getResult numAlloc σ).push
          ((idx.eq ((HashConsM.mkConstant (len : ZMod p)).getResult ((oneHotRaw len idx).getHashConsState numAlloc σ))).getResult
          ((oneHotRaw len idx).getNumAlloc numAlloc σ)
          ((HashConsM.mkConstant (len : ZMod p)).getHashConsState ((oneHotRaw len idx).getHashConsState numAlloc σ)))
      := by
        simp [eq]
      rewrite [this]; clear this
      rewrite [Convert.toIdeal_push]
      . rfl
      . simp [eq]
        rewrite [ClapM.getVarStore_bind_of_wellFormed (wellFormed h_idx_val h_idx_varSet)]
        . done
        . apply ClapM.bind_wellFormed
          . grind
          . simp
            apply F.eq.wellFormed
            . have h_toIdeal : (F.Convert.toIdeal varStore σ idx).isSome = true := by aesop
              have := wellFormed_of_toIdeal_isSome h_toIdeal

              done
          done
        done
      done

    simp [this, ih]
    rewrite [toIdeal_eq_toIdeal_of_wellFormed, h_idx_val]
    . aesop
    . apply wellFormed_of_toIdeal_isSome (varStore := varStore)
      grind
    . grind
    . exact wellFormed h_idx_val h_idx_varSet
  done

end oneHotRaw

end F

end Clap.Lang
