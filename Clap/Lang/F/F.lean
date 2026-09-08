import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert
import Clap.Lang.F.Extensions

import Clap.Lang.Wheels

namespace Clap.Lang

variable {p : ℕ}

abbrev F := ExprRef
abbrev FB := F
abbrev FArray (k) := Vector FB k -- TODO FB_Vector?
abbrev FList := List FB

section Converts

namespace F

abbrev conversion : Conversion p F where
  IdealT := ZMod p
  toExprs x := [x]
  conversion x := [x]

end F


namespace FB

abbrev conversion : Conversion p FB where
  IdealT := Bool
  toExprs x := [x]
  conversion x := [if x then 1 else 0]

end FB


namespace FUnit

abbrev conversion : Conversion p Unit where
  IdealT := Unit
  toExprs _ := []
  conversion _ := []

end FUnit


namespace FArray

abbrev conversion {k} : Conversion p (FArray k) where
  IdealT := Vector Bool k
  toExprs x := x.toList
  conversion x := (x.map fun x ↦ if x then 1 else 0).toList

end FArray


namespace FList

abbrev conversion : Conversion p FList where
  IdealT := List Bool
  toExprs x := x
  conversion x := x.map fun x ↦ if x then 1 else 0

end FList

end Converts


section ConvertsLemmas

namespace F

lemma converts_of_FB_converts
  {state : ClapMState p}
  {expr : FB}
  {b : Bool}
  (h : Converts FB.conversion state expr b)
:
  Converts F.conversion state expr (if b then (1 : ZMod p) else (0 : ZMod p))
:= converts_cast
  (conversion1 := FB.conversion)
  (conversion2 := F.conversion)
  (y := expr)
  (val2 := if b then (1 : ZMod p) else (0 : ZMod p))
  h (by rfl) (by rfl)

end F

namespace FB

lemma converts_of_F_converts
  [p.AtLeastTwo]
  {state : ClapMState p}
  {expr : F}
  {val}
  (h : Converts F.conversion state expr val)
  (h_val : val.val < 2)
:
  Converts FB.conversion state (expr : FB) (val == 1)
:= by
  apply converts_cast h
  . rfl
  . unfold F.conversion conversion
    simp
    split
    . trivial
    next h_neq =>
      rewrite [←ZMod.val_eq_zero]
      rewrite [←ZMod.val_eq_one] at h_neq
      grind
      exact Nat.AtLeastTwo.one_lt 

end FB


namespace FUnit

lemma converts
  {state : ClapMState p}
  {exprs}
  {val}
:
  Converts FUnit.conversion state exprs val
:= by
  grind [Converts]

end FUnit


namespace FArray

@[simp]
lemma converts_empty
  {state : ClapMState p}
:
  Converts conversion state #v[] #v[]
:= by
  constructor
  . grind
  · grind
  · grind
  · grind

lemma converts_iff_FB_converts
  {k}
  {state : ClapMState p}
  {exprs : FArray k}
  {val : Vector Bool k}
:
  Converts conversion state exprs val ↔
  (∀ i : Fin k, Converts FB.conversion state exprs[i] val[i])
:= by
  constructor
  . intro h ⟨i, h_i⟩
    constructor
    . intro ⟨ib, h_ib⟩
      simp
      convert h.varSet_wf ⟨i, by grind⟩
      simp [conversion]
    . intro ⟨ib, h_ib⟩
      simp
      convert h.expr_wf ⟨i, by grind⟩
      simp [conversion]
    . intro ⟨ib, h_ib⟩
      simp
      convert h.value_eq ⟨i, by grind⟩
      . simp [conversion]
      . simp [conversion]
    . rfl
  . intro h
    constructor
    . intro ⟨i, h_i⟩
      convert (h ⟨i, by grind⟩).varSet_wf
      simp [conversion]
    . intro ⟨i, h_i⟩
      convert (h ⟨i, by grind⟩).expr_wf
      simp [conversion]
    . intro ⟨i, h_i⟩
      convert (h ⟨i, by grind⟩).value_eq
      simp [conversion]
    . grind

lemma converts_push
  {k}
  {state : ClapMState p}
  {exprs : Vector FB k}
  {expr : FB}
  {vals : Vector Bool k}
  {val : Bool}
  (h_exprs : Converts conversion state exprs vals)
  (h_expr : Converts FB.conversion state expr val)
:
  Converts conversion state (exprs.push expr) (vals.push val)
:= by
  rewrite [converts_iff_FB_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  by_cases i = k
  . convert h_expr
    . grind
    . grind
  . convert (h_exprs ⟨i, by grind⟩) using 1
    . grind
    . grind

lemma convertsM_of_convertsM_toList
  {k}
  {action : ClapM p (Vector FB k)}
  {state}
  {val : Vector Bool k}
  (h : ConvertsM FList.conversion (Vector.toList <$> action) state val.toList)
:
  ConvertsM conversion action state val
:= by
  constructor
  . obtain ⟨⟨_, _, _, _⟩, _, _⟩ := h
    constructor <;> simp at *
    . assumption
    . assumption
    . assumption
  . grind [h.wellFormed]
  . grind [h.constraints, ClapM.runAndEval]

lemma converts_vector_cast
  {k1 k2}
  {state : ClapMState p}
  {exprs : FArray k1}
  {val : Vector Bool k1}
  (h : Converts conversion state exprs val)
  (h_k : k1 = k2)
:
  Converts conversion state (exprs.cast h_k) (val.cast h_k)
:= by
  rewrite [converts_iff_FB_converts] at ⊢ h
  intro ⟨i, h_i⟩
  exact h ⟨i, by grind⟩

lemma converts_pop
  {k}
  {state : ClapMState p}
  {exprs : FArray k}
  {val : Vector Bool k}
  (h : Converts conversion state exprs val)
:
  Converts conversion state (exprs.pop) (val.pop)
:= by
  rewrite [converts_iff_FB_converts] at ⊢ h
  intro ⟨i, h_i⟩
  convert (h ⟨i, by grind⟩) using 1
  . grind
  . grind

lemma converts_getElem
  {k i}
  {state : ClapMState p}
  {exprs : FArray k}
  {vals : Vector Bool k}
  (h : Converts conversion state exprs vals)
  (h_i : i < k)
:
  Converts FB.conversion state exprs[i] vals[i]
:= (converts_iff_FB_converts.mp h) ⟨i, h_i⟩

end FArray


namespace FList

@[simp]
lemma converts_empty
  {state : ClapMState p}
: Converts conversion state [] [] := by
  constructor
  . simp
  · simp
  · grind
  · grind

lemma converts_append
  {state : ClapMState p}
  {exprs1 exprs2 : List FB}
  {vals1 vals2 : List Bool}
  (h_exprs1 : Converts FList.conversion state exprs1 vals1)
  (h_exprs2 : Converts FList.conversion state exprs2 vals2)
:
  Converts FList.conversion state (exprs1 ++ exprs2) (vals1 ++ vals2)
:= by
  obtain ⟨exprs1_length, exprs1_varSet, exprs1_wellFormed, exprs1_result⟩ := h_exprs1
  obtain ⟨exprs2_lengh, exprs2_varSet, exprs2_wellFormed, exprs2_result⟩ := h_exprs2
  simp at *
  constructor
  . intro i
    simp [List.getElem_append]
    split
    . exact exprs1_varSet ⟨i.val, by grind⟩
    . exact exprs2_varSet ⟨_, by grind⟩
  . intro i
    simp [List.getElem_append]
    split
    . exact exprs1_wellFormed ⟨i.val, by grind⟩
    . exact exprs2_wellFormed ⟨_, by grind⟩
  . intro i
    simp [List.getElem_append, exprs1_length]
    split
    . exact exprs1_result ⟨i.val, by grind⟩
    . exact exprs2_result ⟨_, by grind⟩
  . grind

lemma converts_of_converts_FB
  {state : ClapMState p}
  {exprs}
  {vals}
  (h_length : exprs.length = vals.length)
  (h_converts : ∀ i : Fin exprs.length, Converts FB.conversion state exprs[i] vals[i])
:
  Converts FList.conversion state exprs vals
:= by
  constructor
  . intro i
    have := (h_converts i).varSet_wf
    simp at this
    assumption
  . intro i
    have := (h_converts i).expr_wf
    simp at this
    assumption
  . intro i
    have := (h_converts i).value_eq
    simp at this
    simp [this]
  . grind

lemma converts_singleton_of_converts_FB
  {state : ClapMState p}
  {expr}
  {val}
  (h_converts : Converts FB.conversion state expr val)
:
  Converts FList.conversion state [expr] [val]
:= by
  apply converts_of_converts_FB
  . simpa
  . simp

end FList

end ConvertsLemmas


namespace eq0

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
:
  (eq0 e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_eq0
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a : F}
:
  Converts FUnit.conversion
    ((eq0 a).getState state)
    ((eq0 a).getResult state.numAlloc state.σ)
    ()
:= by
  constructor <;> simp at *

lemma constraints
  {state : ClapMState p}
  {a}
  (h_a : Converts F.conversion state a (0 : ZMod p))
:
  ((eq0 a).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  simp
  have := h_a.value_eq
  simp at this
  exact this

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a : F}
  (h_a : Converts F.conversion state a (0 : ZMod p))
:
  ConvertsM FUnit.conversion (eq0 a)
    state
    ()
where
  result := converts
  wellFormed := wellFormed h_a
  constraints := constraints h_a

end eq0


namespace isZero

@[simp, grind! .]
lemma lt_getNumAlloc
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : ExprRef}
:
  numAlloc < (isZero a).getNumAlloc numAlloc σ
:= by
  simp [isZero]

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
:
  (isZero e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_isZero
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  [p.AtLeastTwo]
  {state}
  {a : F}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  Converts FB.conversion
    ((isZero a).getState state)
    ((isZero a).getResult state.numAlloc state.σ)
    (a_val == 0)
:= by
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨varStore, σ, numAlloc⟩ := state
  simp [ClapM.getState]
  constructor <;> simp at *
  . intro i h_i
    grind [=isZero, ClapM.getState]
  . simp [isZero]
    rw [Expr.wellFormed_iff_isSome, Expr.deref_mkVar_eq_some]
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

lemma constraints
  {state : ClapMState p}
  {a}
  {a_val}
  (h_a : Converts F.conversion state a a_val)
:
  ((isZero a).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  simp
  have : [state.varStore|⦃a, state.σ⦄].isSome := by grind
  exact isSome_eval_of_prefix (by {
    grind [cases Converts]
  }) this (by rfl) (by grind)

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a : F}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM FB.conversion (isZero a)
    state
    (a_val == 0)
where
  result := converts h_a
  wellFormed := wellFormed h_a
  constraints := constraints h_a

end isZero


namespace mkAdd

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : Converts F.conversion state a a_val)
   (h_b : Converts F.conversion state b b_val)
:
  Converts F.conversion
    (ClapM.getState (liftM (HashConsM.mkAdd (p := p) a b)) state)
    (ClapM.getResult (liftM (HashConsM.mkAdd (p := p) a b)) state.numAlloc state.σ)
    (a_val + b_val)
:= by
  simp [ClapM.getState]
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_length, b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . grind

lemma constraints
  {state : ClapMState p}
  {a b}
:
  ((liftM (n := ClapM p) (HashConsM.mkAdd (p := p) a b)).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  grind [ClapM.runAndEval]

lemma convertsM
  {state}
  {a b : ExprRef}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM F.conversion (liftM (HashConsM.mkAdd (p := p) a b)) state (a_val + b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkAdd
  constraints := constraints

end mkAdd


namespace mkSub

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : Converts F.conversion state a a_val)
   (h_b : Converts F.conversion state b b_val)
:
  Converts F.conversion
    (ClapM.getState (liftM (HashConsM.mkSub (p := p) a b)) state)
    (ClapM.getResult (liftM (HashConsM.mkSub (p := p) a b)) state.numAlloc state.σ)
    (a_val - b_val)
:= by
  simp [ClapM.getState]
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_length, b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . grind

lemma constraints
  {state : ClapMState p}
  {a b}
:
  ((liftM (n := ClapM p) (HashConsM.mkSub (p := p) a b)).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  grind [ClapM.runAndEval]

lemma convertsM
  {state}
  {a b : ExprRef}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM F.conversion (liftM (HashConsM.mkSub (p := p) a b)) state (a_val - b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkSub
  constraints := constraints

end mkSub


namespace mkMul

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : Converts F.conversion state a a_val)
   (h_b : Converts F.conversion state b b_val)
:
  Converts F.conversion
    (ClapM.getState (liftM (HashConsM.mkMul (p := p) a b)) state)
    (ClapM.getResult (liftM (HashConsM.mkMul (p := p) a b)) state.numAlloc state.σ)
    (a_val * b_val)
:= by
  simp [ClapM.getState]
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_length, b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . grind

lemma constraints
  {state : ClapMState p}
  {a b}
:
  ((liftM (n := ClapM p) (HashConsM.mkMul (p := p) a b)).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  grind [ClapM.runAndEval]

lemma convertsM
  {state}
  {a b : ExprRef}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM F.conversion (liftM (HashConsM.mkMul (p := p) a b)) state (a_val * b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkMul
  constraints := constraints

end mkMul


section eq

def eq {p : ℕ} [p.AtLeastTwo] (a b : F) : ClapM p FB := do
  isZero (←HashConsM.mkSub (p := p) a b)

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a b : F}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (eq a b) state (a_val == b_val)
:= by
  unfold eq

  have this := mkSub.convertsM h_a h_b
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  have := isZero.convertsM this.result
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  constructor
  . convert this.result using 1
    . grind
    . grind [ClapM.getState]
    . grind
  . grind [ClapM.getState]
  . grind [ClapM.getState]

end eq
end eq


namespace MkConstant

@[simp]
lemma convertsM
  {state}
  {x : ZMod p}
:
  ConvertsM F.conversion (liftM (HashConsM.mkConstant (p := p) x)) state x
:= by
  constructor
  · simp [ClapM.getState]
    simp_rw [HashConsM.getResult_mkConstant, HashConsM.getHashConsState_mkConstant]
    constructor <;> simp
    · grind [=Expr.varSet, =Expr.varSet_wellFormed]
    · grind
    · rw [eval_eq_evalRec (by grind)]
      grind
  · grind
  . grind [ClapM.runAndEval]

end MkConstant


section OneHotRaw

open HashConsM

variable {p : ℕ} [p.AtLeastTwo] {start len : ℕ} {idx : F} {numAlloc : ℕ} {σ : HashConsSt p}

def oneHotRaw_aux (start len : ℕ) (idx : F) : ClapM p (Vector FB len) :=
  (Vector.range' start len).mapM (fun (i:ℕ) ↦ do
    let idx_val ← mkConstant (p := p) i
    eq idx idx_val
  )

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

def oneHotRaw (len : ℕ) (idx : F) : ClapM p (FArray len) :=
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

namespace oneHotRaw

omit [p.AtLeastTwo] in
lemma convertsM_map_FArray_FArray
  {k1 k2}
  (action : ClapM p (Vector FB k1))
  (f : Vector FB k1 → Vector FB k2)
  (state)
  {action_val : Vector Bool k1}
  (f_val : Vector Bool k1 → Vector Bool k2)
  (h_action : ConvertsM FArray.conversion action state action_val)
  (h_f_val : Converts FArray.conversion
    (action.getState state)
    (f (action.getResult state.numAlloc state.σ))
    (f_val action_val)
  )
:
  ConvertsM FArray.conversion (f <$> action) state (f_val action_val)
:= by
  constructor
  . simp
    apply h_f_val
  . rewrite [ClapM.map_wellFormed]
    apply h_action.wellFormed
  . grind [ClapM.runAndEval, h_action.constraints]

omit [p.AtLeastTwo] in
@[grind .]
lemma bind_wellFormed'
  {α β}
  {a : ClapM p α}
  {f : α → ClapM p β}
  {state: ClapMState p}
  (h_a : a.wellFormed state.numAlloc state.varStore state.σ)
  (h_f : (f (a.getResult state.numAlloc state.σ)).wellFormed
    (a.getState state).numAlloc
    (a.getState state).varStore
    (a.getState state).σ
  )
:
  (a >>= f).wellFormed state.numAlloc state.varStore state.σ
:= by
  apply ClapM.bind_wellFormed h_a
  grind [ClapM.getState]

namespace X

def y : Nat := 42
end X

section

open Lean Elab Tactic Meta

def baseNamespace := Name.mkStr2 "Clap" "Lang"

def lemmaOfIdentifiers (prefixNamespace lemmaName : Name) : MetaM ConstantInfo := do
  let name := baseNamespace ++ prefixNamespace ++ lemmaName
  let .some «lemma» := (←getEnv).find? name
    | throwError m!"Undeclared constant: {name}"
  return «lemma»

def convertsMargs (convertsME convertsMT : Lean.Expr) (goal : MVarId) :
  MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := goal.withContext do
  -- logInfo m!"In"
  let convertsMT ← instantiateMVars convertsMT
  -- logInfo m!"Instantiated"
  match_expr convertsMT with
    | Clap.ConvertsM p α _ action state _ => return (
        -- ←Expr.mkDirectProjection convertsMT `result,
        ←mkAppM ``Clap.ConvertsM.result #[convertsME],
        -- ←Expr.mkDirectProjection convertsMT `wellFormed,
        ←mkAppM ``Clap.ConvertsM.wellFormed #[convertsME],
        -- ←Expr.mkDirectProjection convertsMT `constraints,
        ←mkAppM ``Clap.ConvertsM.constraints #[convertsME],
        p,
        α,
        action,
        state
      )
    | _ => panic! "Not a convertsM"


-- def convertsLemmaAndStateOfType (convertsT : Lean.Expr) : MetaM (ConstantInfo × Lean.Expr) := do
--   let convertsT ← instantiateMVars convertsT
--   let (prefixNamespace, st) :=
--     match_expr convertsT with
--     | Clap.Lang.FList.Converts _ st _ _ => (`FList, st)
--     | Clap.Lang.FArray.Converts _ st _ _ => (`FArray, st)
--     | Clap.Lang.FUnit.Converts _ st _ _ => (`FUnit, st)
--     | Clap.Lang.FB.Converts _ st _ _ => (`FB, st)
--     | Clap.Lang.F.Converts _ st _ _ => (`F, st)
--     | _ => unreachable!
--   return (←lemmaOfIdentifiers prefixNamespace `converts_skip, st)

def _root_.Lean.Meta.Hypothesis.ofNameValue (userName : Name) (value : Lean.Expr) : MetaM Hypothesis := do
  return {
    userName := userName
    type     := ←inferType value
    value    := value
  }

def _root_.Lean.MVarId.set (goal : MVarId) (name : Name) (rhs : Term) : MetaM MVarId := do
  let ident := mkIdent name
  let ([goal], _) ← runTactic goal (←`(tactic| set $ident:ident := $rhs))
    | throwError m!"set failed (rhs := {rhs})"
  return goal

/--
Execute `set`s in order, ensuring the local context is updated between every invocation.
-/
def _root_.Lean.MVarId.setManyInOrder (goal : MVarId) (nameXrhs : List (Name × Term)) : MetaM MVarId :=
  nameXrhs.foldlM (fun acc (name, rhs) ↦ do acc.withContext do acc.set name rhs) goal

/--
Yields tuples `(namespace, fvar, state, type)` of local hypotheses of the shape `<_>.Converts`.
-/
def stateAssertions (goal : MVarId) :
  MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := goal.withContext do
  let allAssertions := (←getLCtx).getFVars
  let allAssertionsT ← allAssertions.filterMapM fun fvar ↦ do
    let type ← instantiateMVars (←inferType fvar)
    return match_expr type with
    | Clap.Converts _ _ _ st _ _ => .some (fvar, st, type)
    | _ => .none
  if (allAssertionsT.groupByKey (fun (_, st, _) ↦ st) |>.size) > 1
  then
    -- logWarning m!"OUR GUY:\n{(allAssertionsT.groupByKey fun (_, _, st, _) ↦ st).toArray}"
    logWarning m!"Assumptions of shape `Converts` refer to multiple states. Are you ~~mad~~ sure?"
  return allAssertionsT

def lemmaOfNextCommand (goal : MVarId) : MetaM (Option Lean.Expr) := do
  let conclusion ← (instantiateMVars (←goal.getType))
  let_expr Clap.ConvertsM _ _ _ action _ _ := conclusion |
    logWarning m!"Cannot infer the next step - expected `Clap.ConvertsM`.\nGot instead:\n{conclusion}"
    return .none
  let ⟨name, _args⟩ := action.getAppFnArgs

  if name == `Bind.bind then logInfo m!"Bind.bind"; return mkConst `Clap.convertsM_bind
  if name == `Functor.map then logInfo m!"Functor.map"; return mkConst `Clap.convertsM_map

  logInfo m!"Conclusion unchanged; spec missing for:\n{action}"
  return .none

def step_impl (convertsME : Lean.Expr) (actionName : Name) (goal : MVarId) : TermElabM MVarId := goal.withContext do
  let convertsMType ← inferType convertsME
  -- logInfo m!"convertsMType : {convertsMType}"
  let (convertsConvertsM, wellFormedConvertsM, constraintsConvertsM, pE, αE, actionE, stateE) ←
    convertsMargs convertsME convertsMType goal
  let stateS ← Term.exprToSyntax stateE
  -- logInfo m!"Done"
  let stepE := convertsConvertsM
  let hypWFE := wellFormedConvertsM
  let hypConstraintsE := constraintsConvertsM

  let stateAssertions ← stateAssertions goal
  let assertions ← stateAssertions.mapM fun (fvar, state, type) ↦ do
    -- let stateS ← Term.exprToSyntax state
    -- let «lemma» ← lemmaOfIdentifiers `converts_skip
    return (fvar, ←mkAppM `Clap.converts_skip #[convertsME, fvar])

  let goal ← assertions.foldlM (init := goal) fun goal (fvar, _) ↦
    goal.clear fvar.fvarId!

  let (_, goal) ← goal.assertHypotheses <|
    #[
      -- ←Hypothesis.ofNameValue `this convertsME,
      ←Hypothesis.ofNameValue (actionName.appendBefore "h_") stepE,
      ←Hypothesis.ofNameValue `h_wellFormed hypWFE,
      ←Hypothesis.ofNameValue `h_constraints hypConstraintsE,
    ] ++ (
      ←assertions.mapM fun (fvar, expr) ↦ do
        let name := ((←getLCtx).get! fvar.fvarId!).userName
        Hypothesis.ofNameValue name expr
    )

  let env ← getEnv
  modifyEnv (fun _ ↦ stepExt.setState env ⟨actionName.appendBefore "h_"⟩)

  let actionIdent := Lean.mkIdent actionName
  -- logInfo m!"actionName: {actionName}"
  -- logInfo m!"actionE: {actionE}"
  goal.setManyInOrder [
    -- `set action := <action_from_monad>`
    (actionName, ←Term.exprToSyntax actionE),
    -- `set <action>_result := <action>.getResult <state>.numAlloc <state>.σ`
    (actionName.appendAfter "_result", ←`($(actionIdent).getResult $(stateS).numAlloc $(stateS).σ)),
    -- `set <state> := <action>.getState <state>`
    (actionName.appendAfter "_state", ←`($(actionIdent).getState $stateS))
  ]

elab "step" convertsM:term "as" actionName:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let convertsME ← instantiateMVars (←elabTerm convertsM .none)
  discard do 
    match ←lemmaOfNextCommand goal with
    | .none => pure ()
    | .some stepConclusion =>
      replaceMainGoal (←goal.apply stepConclusion)
      let goal ← getMainGoal
      replaceMainGoal (←goal.apply convertsME)
  let goal ← step_impl convertsME actionName.getId (←getMainGoal)
  replaceMainGoal [goal]

elab "finish" : tactic => withMainContext do
  let target ← whnf (←getMainTarget)

  logInfo m!"target: {target}\n{repr target}"

  if !target.isAppOf ``Clap.ConvertsM
  then logWarning m!"Made no progress - the concluson must be of shape ConvertsM."
       return ()

  let result :: goalsRest ← (←getMainGoal).constructor | unreachable!
  for goal in goalsRest do
    try
      let ([], _) ← runTactic goal (←`(tactic| grind)) | continue
    catch _ =>
      continue
  
  let goalsRest ← goalsRest.filterM fun goal ↦ return !(←goal.isAssigned)

  let lastConvertsM := stepExt.getState (← getEnv) |>.lastLemmaUserName
  let lastConvertsME := (←getLCtx).getFromUserName! lastConvertsM |>.toExpr
  
  -- let [result] ← result.apply (mkConst ``Clap.converts_of_converts)
  --   | logWarning m!"Failed to apply: {``Clap.converts_of_converts}"

  replaceMainGoal (result :: goalsRest)


  logInfo m!"hyp: {lastConvertsME}"

end

lemma convertsM_but_sane?
  {state}
  {len : ℕ}
  {idx : F}
  {idx_val : ZMod p} -- TODO : Fin len?
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (oneHotRaw len idx) state (Vector.ofFn (λ x => x.val == idx_val.val))
:= by
  apply FArray.convertsM_of_convertsM_toList
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
  have not_this : ∀ x ∈ list, x < p := by grind
  clear_value list

  rw [←list.reverse_reverse] at not_this ⊢
  set list := list.reverse
  clear_value list
  induction' eq_ih : list.length with len h_len generalizing list
  . aesop
  . rcases list with _ | ⟨hd, tl⟩
    · grind
    · simp

      specialize h_len tl (by aesop (add safe (by grind))) (by grind)
      simp at h_len

      step h_len as yourFace
      step @MkConstant.convertsM p yourFace_state hd as myFace
      step eq.convertsM h_idx h_myFace as eq

      apply FList.converts_append h_yourFace
      apply FList.converts_singleton_of_converts_FB
      apply converts_of_converts h_eq

      rewrite [←ZMod.val_cast_of_lt (a := hd) (not_this hd (by grind))]
      simp only [ZMod.val_natCast, beq_eq_beq]
      apply Iff.intro
      . intro h
        simp [h]
      . intro h
        simp [h]

end oneHotRaw
end OneHotRaw

section assert_eq

def assert_eq (a b : F) : ClapM p Unit := do
  let diff ← HashConsM.mkSub (p := p) a b
  eq0 diff

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {a b} {val}
  {state : ClapMState p}
  (h_a : Converts F.conversion state a val)
  (h_b : Converts F.conversion state b val)
:
  ConvertsM FUnit.conversion (assert_eq a b) state ()
:= by
  unfold assert_eq

  step mkSub.convertsM h_a h_b as sub
  -- TODO adjust to not assume constraints
  simp at h_sub
  step eq0.convertsM h_sub as eq0
  constructor
  . apply FUnit.converts
  . assumption
  . assumption

end assert_eq
end assert_eq

section sum

open HashConsM in
def FArray.sum' {k} (init : F) (vals : FArray k) : ClapM p F := do
  vals.foldlM (λ x y => liftM (mkAdd (p := p) x y)) init

namespace FArray.sum'

lemma convertsM
  {k}
  {state : ClapMState p}
  {f_vals : FArray k}
  {vals : Vector Bool k}
  {init : F}
  (h_vals : Converts FArray.conversion state f_vals vals)
  (h_init : Converts F.conversion state init 0)
:
  ConvertsM F.conversion (f_vals.sum' init) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum
:= by
  unfold sum'

  induction' k with k h_k
  . have (init : ExprRef) : Vector.foldlM (λ x y => liftM (n := ClapM p) (HashConsM.mkAdd (p := p) x y)) init f_vals = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := f_vals
      grind
    simp [this]

    apply convertsM_pure

    have : vals = #v[] := by grind
    simp [this]
    assumption
  . have := (FArray.converts_vector_cast (k2 := k) (FArray.converts_pop h_vals) (by trivial))
    set fvals_base := Vector.cast (m := k) (by trivial) f_vals.pop
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop

    have h_push : f_vals = fvals_base.push f_vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [fvals_base]
      . grind
    rewrite [h_push]
    simp [Vector.foldlM_push]

    step @h_k fvals_base vals_base this as mapM
    have h_fvals_k := F.converts_of_FB_converts (FArray.converts_getElem h_vals (Nat.lt_succ_self k))
    step mkAdd.convertsM h_mapM h_fvals_k as add

    finish
    sorry
    -- constructor
    -- . apply converts_of_converts h_add
    --   have : vals = vals_base.push vals[k] := by
    --     ext
    --     rewrite [Vector.getElem_push]
    --     split
    --     . simp [vals_base]
    --     . grind
    --   rewrite [this]
    --   simp
    

end FArray.sum'



open HashConsM in
def FArray.sum {k} (vals : FArray k) : ClapM p F := do
  vals.foldlM (λ x y => liftM (mkAdd (p := p) x y)) (←liftM (mkConstant (0 : ZMod p)))

namespace FArray.sum

lemma convertsM
  {k}
  {state : ClapMState p}
  {f_vals : FArray k}
  {vals : Vector Bool k}
  (h_vals : Converts FArray.conversion state f_vals vals)
:
  ConvertsM F.conversion (f_vals.sum) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum
:= by
  unfold sum
  simp [←sum'.eq_def]

  step MkConstant.convertsM as zero
  step sum'.convertsM h_vals h_zero as sum'

  constructor
  . grind
  . assumption
  . assumption

end FArray.sum
end sum

section singleOneArray

/-- Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere. Only satisfiable when `0 ≤ idx < len`. -/
def singleOneArray [p.AtLeastTwo] (len : ℕ) (idx : F) : ClapM p (FArray len) := do
  let out ← oneHotRaw len idx
  let s : F ← out.sum
  assert_eq s (←liftM (HashConsM.mkConstant (1 : ZMod p)))
  return out

namespace singleOneArray

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {state}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
  (h_idx_val : idx_val.val < len)
:
  ConvertsM FArray.conversion (singleOneArray len idx) state (Vector.ofFn (λ x => x.val == idx_val.val))
:= by
  unfold singleOneArray

  step oneHotRaw.convertsM_but_sane? h_idx h_len as oneHot
  step FArray.sum.convertsM h_oneHot as sum
  -- lean stack overflows while typing these, but succeeds when they are done
  -- TODO better error handling?
  step MkConstant.convertsM as one

  have : (Vector.ofFn ((fun x => if x = true then 1 else 0) ∘ (λ x : Fin len => x == idx_val.val))).sum = (1 : ZMod p) := by
    clear *-h_len h_idx_val
    induction' len with len ih
    . grind
    . specialize ih (by grind)
      rewrite [Vector.ofFn_succ]
      by_cases h: idx_val.val = len
      . simp [h]
        clear ih
        have (i : Fin len) : (i.val = len) = false := by grind
        simp [this]
        clear *-len
        unfold Vector.ofFn
        simp
        induction' len with len ih'
        . set x := Array.ofFn _
          have : x = #[] := rfl
          grind
        . rewrite [Array.ofFn_succ]
          grind
      . specialize ih (by grind)
        simp
        rewrite [ite_cond_eq_false]
        . simp
          convert ih
          grind
        . grind

  have h_sum : Converts F.conversion one_state sum_result 1 := by
    convert h_sum
    rw [←this]
    simp
    congr
    funext
    rw [this]

  step assert_eq.convertsM h_sum h_one as assert_eq

  apply convertsM_pure

  assumption

end singleOneArray

end singleOneArray




end Clap.Lang
