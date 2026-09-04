import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert

import Clap.Lang.Wheels

namespace Clap.Lang

variable {p : ℕ}

abbrev F := ExprRef
abbrev FB := F
abbrev FArray (k) := Vector FB k -- TODO FB_Vector?
abbrev FList := List FB

section Converts

namespace F

abbrev toExprs (x : F) : List ExprRef := [x]
abbrev serializeVal (x : ZMod p) : List (ZMod p) := [x]

def Converts
  (state : ClapMState p)
  (expr : F)
  (val : ZMod p)
:=
  Clap.Converts serializeVal state (toExprs expr) val

def ConvertsM
  (action : ClapM p F)
:=
  Clap.ConvertsM serializeVal (toExprs <$> action)

end F


namespace FB

abbrev toExprs (x : FB) : List ExprRef := [x]
abbrev serializeVal (x : Bool) : List (ZMod p) := [if x then 1 else 0]

def Converts
  (state : ClapMState p)
  (expr : FB)
  (val : Bool)
:=
  Clap.Converts serializeVal state (toExprs expr) val

def ConvertsM
  (action : ClapM p FB)
:=
  Clap.ConvertsM serializeVal (toExprs <$> action)

end FB


namespace FUnit

abbrev toExprs (_ : Unit) : List ExprRef := []
abbrev serializeVal (_ : Unit) : List (ZMod p) := []

def Converts
  (state : ClapMState p)
  (expr : Unit)
  (val : Unit)
:=
  Clap.Converts serializeVal state (toExprs expr) val

def ConvertsM
  (action : ClapM p Unit)
:=
  Clap.ConvertsM serializeVal (toExprs <$> action)

end FUnit


namespace FArray

abbrev toExprs {k} (x : FArray k) : List ExprRef := x.toList
abbrev serializeVal {k} (x : Vector Bool k) : List (ZMod p) := (x.map fun x ↦ if x then 1 else 0).toList

def Converts
  {k}
  (state : ClapMState p)
  (exprs : FArray k)
  (vals : Vector Bool k)
:=
  Clap.Converts serializeVal state (toExprs exprs) vals

def ConvertsM {k}
  (action : ClapM p (FArray k))
  (state : ClapMState p)
  (vals : Vector Bool k)
:=
  Clap.ConvertsM serializeVal (toExprs <$> action) state vals

end FArray


namespace FList

abbrev toExprs (x : FList) : List ExprRef := x
abbrev serializeVal (x : List Bool) : List (ZMod p) := x.map fun x ↦ if x then 1 else 0

def Converts
  (state : ClapMState p)
  (exprs : List FB)
  (val : List Bool)
:= Clap.Converts
  (fun l : List Bool ↦ l.map fun x ↦ if x then 1 else 0)
  state
  exprs
  val

def ConvertsM
  (action : ClapM p FList)
  (state : ClapMState p)
  (val : List Bool)
:= Clap.ConvertsM
  (fun l : List Bool ↦ l.map fun x ↦ if x then 1 else 0)
  action
  state
  val

end FList

end Converts


section ConvertsLemmas

namespace F

lemma converts_of_convertsM
  {action : ClapM p F}
  {state} {val}
  (h : (ConvertsM action state val))
:
  Converts (action.getState state) (action.getResult state.numAlloc state.σ) val
:= by
  convert h.result
  simp [Converts]

structure Spec (state) where
  action : ClapM p F
  spec : ZMod p
  converts : ConvertsM action state spec

@[aesop unsafe apply]
lemma converts_skip
  {α} {conversion}
  {skip : ClapM p (List ExprRef)} {state}
  {val' : α} {expr : F} {val : ZMod p}
  (h_skip : Clap.ConvertsM conversion skip state val')
  (h : Converts state expr val)
:
  Converts (skip.getState state)
           expr
           val
:=
  Clap.converts_skip h_skip h

@[aesop safe]
lemma convertsM_pure
        {state : ClapMState p}
        {x : F}
        {val : ZMod p}
        (h : F.Converts state x val)
  : ConvertsM (pure x) state val := by
  constructor
  · simpa
  · grind
  . simp [ClapM.runAndEval]

lemma converts_of_FB_converts
  {state : ClapMState p}
  {expr : FB}
  {b}
  (h : FB.Converts state expr b)
:
  Converts state expr (if b then 1 else 0)
:= by
  obtain ⟨_, _, _, _⟩ := h
  constructor <;> simp_all

end F


namespace FB

lemma converts_of_convertsM
  {action : ClapM p F}
  {state} {val}
  (h : (ConvertsM action state val))
:
  Converts (action.getState state) (action.getResult state.numAlloc state.σ) val
:= by
  convert h.result
  simp [Converts]

/-
Best not to use because unification struggles to pick out function_val
Instead, build forwards, applying action and function to the state in order
-/
lemma convertsM_bind_F
  (action : ClapM p F)
  (function : F → ClapM p FB)
  (state)
  {action_val : ZMod p}
  (function_val : ZMod p → Bool)
  (h_action : F.ConvertsM action state action_val)
  (h_function : FB.ConvertsM
    (function (action.getResult state.numAlloc state.σ))
    (action.getState state)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) state (function_val action_val)
:= by
  constructor
  . simp [ClapM.getState]
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . obtain ⟨_,_,a_constraints⟩ := h_action
    obtain ⟨_,_,f_constraints⟩ := h_function
    grind [ClapM.getState]


structure Spec (state) where
  action : ClapM p FB
  spec : Bool
  converts : ConvertsM action state spec

end FB


namespace FArray

lemma converts_of_convertsM
  {k}
  {action : ClapM p (FArray k)}
  {state} {val}
  (h : (ConvertsM action state val))
:
  Converts (action.getState state) (action.getResult state.numAlloc state.σ) val
:= by
  convert h.result
  simp [Converts]

lemma converts_skip
  {k1} {α} {conversion}
  {skip : ClapM p (List ExprRef)} {state}
  {val : Vector Bool k1} {val' : α} {exprs : Vector ExprRef k1}
  (h_skip : Clap.ConvertsM conversion skip state val')
  (h : FArray.Converts state exprs val) :
  FArray.Converts (skip.getState state)
                   exprs
                   val := by
  rcases eq! : h
  rcases h_skip
  constructor
  · grind [=Expr.varSet_wellFormed, ClapM.getState]
  · grind [ClapM.getState]
  next _ _ _ _ _ H _ =>
    intro i
    unfold ClapM.getState ClapM.getVarStore
    rw [eval_varStore_eval_eq_some h]
    exact H.2.2
  · exact h.1

lemma convertsM_bind_F
  {k}
  (action : ClapM p F)
  (function : F → ClapM p (Vector ExprRef k))
  (state)
  {action_val : ZMod p}
  (function_val : ZMod p → Vector Bool k)
  (h_action : F.ConvertsM action state action_val)
  (h_function : FArray.ConvertsM
    (function (action.getResult state.numAlloc state.σ))
    (action.getState state)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) state (function_val action_val)
:= by
  constructor
  . simp [ClapM.getState]
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . rewrite [Circuit.runAndEval_map_constraints, Circuit.runAndEval_bind_constraints]
    . exact ⟨h_action.constraints, h_function.constraints⟩
    . exact h_action.wellFormed
    . grind [ClapM.getState, FArray.ConvertsM, cases Clap.ConvertsM]

lemma convertsM_bind_FB
  {k}
  (action : ClapM p FB)
  (function : FB → ClapM p (Vector ExprRef k))
  (state)
  {action_val : Bool}
  (function_val : Bool → Vector Bool k)
  (h_action : FB.ConvertsM action state action_val)
  (h_function : FArray.ConvertsM
    (function (action.getResult state.numAlloc state.σ))
    (action.getState state)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) state (function_val action_val)
:= by
  constructor
  . simp [ClapM.getState]
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . rewrite [Circuit.runAndEval_map_constraints, Circuit.runAndEval_bind_constraints]
    . exact ⟨h_action.constraints, h_function.constraints⟩
    . exact h_action.wellFormed
    . grind [ClapM.getState, FArray.ConvertsM, cases Clap.ConvertsM]

lemma convertsM_bind_FArray
  {k1 k2}
  (action : ClapM p (Vector FB k1))
  (function : Vector FB k1 → ClapM p (Vector FB k2))
  (state)
  {action_val : Vector Bool k1}
  (function_val : Vector Bool k1 → Vector Bool k2)
  (h_action : FArray.ConvertsM action state action_val)
  (h_function : FArray.ConvertsM
    (function (action.getResult state.numAlloc state.σ))
    (action.getState state)
    (function_val action_val)
  )
:
  ConvertsM (action >>= function) state (function_val action_val)
:= by
  constructor
  . simp [ClapM.getState]
    rewrite [ClapM.getVarStore_bind_of_wellFormed]
    . apply h_function.result
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . apply ClapM.bind_wellFormed
    . apply h_action.wellFormed
    . apply h_function.wellFormed
  . rewrite [Circuit.runAndEval_map_constraints, Circuit.runAndEval_bind_constraints]
    . exact ⟨h_action.constraints, h_function.constraints⟩
    . exact h_action.wellFormed
    . grind [ClapM.getState, FArray.ConvertsM, cases Clap.ConvertsM]

lemma convertsM_map_FB_FArray
  {k}
  (action : ClapM p FB)
  (f : FB → Vector FB k)
  (state)
  {action_val : Bool}
  (f_val : Bool → Vector Bool k)
  (h_action : FB.ConvertsM action state action_val)
  (h_f_val : FArray.Converts
    (action.getState state)
    (f (action.getResult state.numAlloc state.σ))
    (f_val action_val)
  )
:
  ConvertsM (f <$> action) state (f_val action_val)
:= by
  constructor
  . simp
    apply h_f_val
  . rewrite [ClapM.map_wellFormed]
    apply h_action.wellFormed
  . simp [ClapM.runAndEval]
    exact h_action.constraints

@[aesop safe]
lemma convertsM_pure
        {k}
        {state : ClapMState p}
        {x : Vector ExprRef k}
        {val : Vector Bool k}
        (h : FArray.Converts state x val)
  : ConvertsM (pure x) state val := by
  constructor
  · simpa
  · grind
  . simp [ClapM.runAndEval]

@[simp]
lemma converts_empty
        {state : ClapMState p}
  : Converts state #v[] #v[] := by
  constructor
  . simp
  · simp
  · grind
  · grind

lemma converts_push
  {k}
  {state : ClapMState p}
  {exprs : Vector FB k}
  {expr : FB}
  {vals : Vector Bool k}
  {val : Bool}
  (h_exprs : FArray.Converts state exprs vals)
  (h_expr : FB.Converts state expr val)
:
  FArray.Converts state (exprs.push expr) (vals.push val)
:= by
  obtain ⟨exprs_length, exprs_varSet, exprs_wellFormed, exprs_result⟩ := h_exprs
  obtain ⟨expr_lengh, expr_varSet, expr_wellFormed, expr_result⟩ := h_expr
  simp at *
  constructor
  . intro i
    simp [Vector.getElem_push]
    split
    . exact exprs_varSet ⟨i.val, by grind⟩
    . assumption
  . intro i
    simp [Vector.getElem_push]
    split
    . exact exprs_wellFormed ⟨i.val, by grind⟩
    . assumption
  . intro i
    simp [Vector.getElem_push]
    split
    . exact exprs_result ⟨i.val, by grind⟩
    . assumption
  . grind

lemma convertsM_of_convertsM_toList
  {k}
  {action : ClapM p (Vector FB k)}
  {state}
  {val : Vector Bool k}
  (h : FList.ConvertsM (Vector.toList <$> action) state val.toList)
:
  FArray.ConvertsM action state val
:= by
  constructor
  . obtain ⟨⟨_, _, _, _⟩, _, _⟩ := h
    constructor <;> simp at *
    . assumption
    . assumption
    . assumption
  . grind [h.wellFormed]
  . grind [h.constraints, ClapM.runAndEval]

lemma converts_cast
  {k1 k2}
  {state : ClapMState p}
  {exprs : FArray k1}
  {val : Vector Bool k1}
  (h : FArray.Converts state exprs val)
  (h_k : k1 = k2)
:
  FArray.Converts state (exprs.cast h_k) (val.cast h_k)
:= by
  obtain ⟨h_len, h_varSet, h_wf, h_value⟩ := h
  constructor
  . intro i
    specialize h_varSet ⟨i.val, by grind⟩
    simp at ⊢ h_varSet
    convert h_varSet
    grind
  . intro i
    specialize h_wf ⟨i.val, by grind⟩
    simp at ⊢ h_wf
    convert h_wf
    grind
  . intro i
    specialize h_value ⟨i.val, by grind⟩
    simp at ⊢ h_value
    convert h_value
    . grind
    . grind
  . grind

lemma converts_pop
  {k}
  {state : ClapMState p}
  {exprs : FArray k}
  {val : Vector Bool k}
  (h : FArray.Converts state exprs val)
:
  FArray.Converts state (exprs.pop) (val.pop)
:= by
  obtain ⟨h_len, h_varSet, h_wf, h_value⟩ := h
  constructor
  . intro i
    specialize h_varSet ⟨i.val, by grind⟩
    simp at ⊢ h_varSet
    convert h_varSet
  . intro i
    specialize h_wf ⟨i.val, by grind⟩
    simp at ⊢ h_wf
    convert h_wf
  . intro i
    specialize h_value ⟨i.val, by grind⟩
    simp at ⊢ h_value
    convert h_value
  . grind

lemma converts_getElem
  {k i}
  {state : ClapMState p}
  {exprs : FArray k}
  {vals : Vector Bool k}
  (h : FArray.Converts state exprs vals)
  (h_i : i < k)
:
  FB.Converts state exprs[i] vals[i]
:= by
  obtain ⟨h_len, h_varSet, h_wf, h_value⟩ := h
  constructor
  . intro ib
    specialize h_varSet ⟨i, by grind⟩
    simp at ⊢ h_varSet
    convert h_varSet
  . intro ib
    specialize h_wf ⟨i, by grind⟩
    simp at ⊢ h_wf
    convert h_wf
  . intro ib
    specialize h_value ⟨i, by grind⟩
    simp at ⊢ h_value
    convert h_value
  . grind

end FArray


namespace FList

lemma converts_of_convertsM
  {action : ClapM p FList}
  {state} {val}
  (h : (ConvertsM action state val))
:
  Converts (action.getState state) (action.getResult state.numAlloc state.σ) val
:= by
  convert h.result
  simp [Converts]

@[aesop safe]
lemma convertsM_pure
        {state : ClapMState p}
        {x : List FB}
        {val : List Bool}
        (h : FList.Converts state x val)
  : ConvertsM (pure x) state val := by
  constructor
  · simpa
  · grind
  . grind [ClapM.runAndEval]

@[simp]
lemma converts_empty
        {state : ClapMState p}
  : Converts state [] [] := by
  constructor
  . simp
  · simp
  · grind
  · grind

lemma converts_skip
  {α} {conversion}
  {skip : ClapM p (List ExprRef)} {state}
  {val' : α} {expr : List FB} {val : List Bool}
  (h_skip : Clap.ConvertsM conversion skip state val')
  (h : FList.Converts state expr val) :
  FList.Converts (skip.getState state)
             expr
             val := toIdeal_run_of_toIdeal _ h_skip.wellFormed h

lemma converts_append
  {state : ClapMState p}
  {exprs1 exprs2 : List FB}
  {vals1 vals2 : List Bool}
  (h_exprs1 : FList.Converts state exprs1 vals1)
  (h_exprs2 : FList.Converts state exprs2 vals2)
:
  FList.Converts state (exprs1 ++ exprs2) (vals1 ++ vals2)
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
  (h_converts : ∀ i : Fin exprs.length, FB.Converts state exprs[i] vals[i])
:
  FList.Converts state exprs vals
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
  (h_converts : FB.Converts state expr val)
:
  FList.Converts state [expr] [val]
:= by
  apply converts_of_converts_FB
  . simpa
  . simp

end FList

end ConvertsLemmas


namespace eq0

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : F.Converts state e! value)
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
  FUnit.Converts
    ((eq0 a).getState state)
    ((eq0 a).getResult state.numAlloc state.σ)
    ()
:= by
  constructor <;> simp at *

lemma constraints
  {state : ClapMState p}
  {a}
  (h_a : F.Converts state a (0 : ZMod p))
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
  (h_a : F.Converts state a (0 : ZMod p))
:
  FUnit.ConvertsM (eq0 a)
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
  (h : F.Converts state e! value)
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
  (h_a : F.Converts state a a_val)
:
  FB.Converts
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
  (h_a : F.Converts state a a_val)
:
  ((isZero a).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  simp
  have : [state.varStore|⦃a, state.σ⦄].isSome := by grind [F.Converts]
  exact isSome_eval_of_prefix (by {
    grind [F.Converts, cases Converts]
  }) this (by rfl) (by grind)

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a : F}
  {a_val : ZMod p}
  (h_a : F.Converts state a a_val)
:
  FB.ConvertsM (isZero a)
    state
    (a_val == 0)
where
  result := converts h_a
  wellFormed := wellFormed h_a
  constraints := constraints h_a

def spec [p.AtLeastTwo]
  {a : F} {state : ClapMState p} {a_val}
  (h: (F.Converts state a a_val))
:
  FB.Spec state
where
  action := isZero a
  spec := a_val == 0
  converts := convertsM h

end isZero


namespace mkAdd

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : F.Converts state a a_val)
   (h_b : F.Converts state b b_val)
:
  F.Converts
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
  (h_a : F.Converts state a a_val)
  (h_b : F.Converts state b b_val)
:
  F.ConvertsM (liftM (HashConsM.mkAdd (p := p) a b)) state (a_val + b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkAdd
  constraints := constraints

def spec
  {a b : F} {state : ClapMState p} {a_val b_val}
  (h_a: (F.Converts state a a_val))
  (h_b: (F.Converts state b b_val))
:
  F.Spec state
where
  action := (liftM (HashConsM.mkAdd (p := p) a b))
  spec := a_val + b_val
  converts := convertsM h_a h_b

end mkAdd


namespace mkSub

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : F.Converts state a a_val)
   (h_b : F.Converts state b b_val)
:
  F.Converts
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
  (h_a : F.Converts state a a_val)
  (h_b : F.Converts state b b_val)
:
  F.ConvertsM (liftM (HashConsM.mkSub (p := p) a b)) state (a_val - b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkSub
  constraints := constraints

def spec
  {a b : F} {state : ClapMState p} {a_val b_val}
  (h_a: (F.Converts state a a_val))
  (h_b: (F.Converts state b b_val))
:
  F.Spec state
where
  action := (liftM (HashConsM.mkSub (p := p) a b))
  spec := a_val - b_val
  converts := convertsM h_a h_b

end mkSub


namespace mkMul

lemma converts
   {state}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : F.Converts state a a_val)
   (h_b : F.Converts state b b_val)
:
  F.Converts
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
  (h_a : F.Converts state a a_val)
  (h_b : F.Converts state b b_val)
:
  F.ConvertsM (liftM (HashConsM.mkMul (p := p) a b)) state (a_val * b_val)
where
  result := converts h_a h_b
  wellFormed := ClapM.wellFormed_liftM_of_hashConsM_wellFormed HashConsM.wellFormed_mkMul
  constraints := constraints

def spec
  {a b : F} {state : ClapMState p} {a_val b_val}
  (h_a: (F.Converts state a a_val))
  (h_b: (F.Converts state b b_val))
:
  F.Spec state
where
  action := (liftM (HashConsM.mkMul (p := p) a b))
  spec := a_val * b_val
  converts := convertsM h_a h_b

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
  (h_a : F.Converts state a a_val)
  (h_b : F.Converts state b b_val)
:
  FB.ConvertsM (eq a b) state (a_val == b_val)
:= by
  unfold eq

  have this := mkSub.convertsM h_a h_b
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  have := isZero.convertsM (F.converts_of_convertsM this)
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
  F.ConvertsM (liftM (HashConsM.mkConstant (p := p) x)) state x
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

def spec
  (x : ZMod p)
  (state : ClapMState p)
:
  F.Spec state
where
  action := (liftM (HashConsM.mkConstant (p := p) x))
  spec := x
  converts := convertsM

-- TODO, see if this can be done generally?
lemma fold_spec {x : ZMod p} (state : ClapMState p):
  (liftM (HashConsM.mkConstant (p := p) x)) =
  (spec x state).action
:= rfl

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
  (h_action : FArray.ConvertsM action state action_val)
  (h_f_val : FArray.Converts
    (action.getState state)
    (f (action.getResult state.numAlloc state.σ))
    (f_val action_val)
  )
:
  FArray.ConvertsM (f <$> action) state (f_val action_val)
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

def convertsMlemmaOfType (convertsMT : Lean.Expr) : MetaM ConstantInfo := do
  let convertsMT ← instantiateMVars convertsMT
  let prefixNamespace :=
    match_expr convertsMT with
    | Clap.Lang.FList.ConvertsM _ _ _ _ => `FList
    | Clap.Lang.FArray.ConvertsM _ _ _ _ => `FArray
    | Clap.Lang.FUnit.ConvertsM _ _ _ _ => `FUnit
    | Clap.Lang.FB.ConvertsM _ _ _ _ => `FB
    | Clap.Lang.F.ConvertsM _ _ _ _ => `F
    | _ => unreachable!
  let name := baseNamespace ++ prefixNamespace ++ convertsMname
  let .some «lemma» := (←getEnv).find? name
    | throwError m!"Undeclared constant: {name}"
  return «lemma»
  where 
    convertsMname := `converts_of_convertsM

def convertsLemmaOfType (convertsT : Lean.Expr) : MetaM ConstantInfo := do
  let convertsT ← instantiateMVars convertsT
  let prefixNamespace :=
    match_expr convertsT with
    | Clap.Lang.FList.Converts _ _ _ _ => `FList
    | Clap.Lang.FArray.Converts _ _ _ _ => `FArray
    | Clap.Lang.FUnit.Converts _ _ _ _ => `FUnit
    | Clap.Lang.FB.Converts _ _ _ _ => `FB
    | Clap.Lang.F.Converts _ _ _ _ => `F
    | _ => unreachable!
  let name := baseNamespace ++ prefixNamespace ++ convertsMname
  let .some «lemma» := (←getEnv).find? name
    | throwError m!"Undeclared constant: {name}"
  return «lemma»
  where 
    convertsMname := `converts_skip

def _root_.Lean.Meta.Hypothesis.ofNameValue (userName : Name) (value : Lean.Expr) : MetaM Hypothesis := do
  return {
    userName := userName
    type     := ←inferType value
    value    := value
  }

def step_impl (convertsME convertsM : Lean.Expr) (goal : MVarId) : MetaM MVarId := goal.withContext do
  let convertsMType ← inferType convertsME
  let convertsType ← inferType convertsM
  -- `Clap.Lang.<type>.convertsOfConvertsM`
  let lemmaConvertsM : ConstantInfo ← convertsMlemmaOfType convertsMType
  let lemmaConverts : ConstantInfo ← convertsLemmaOfType convertsType
  let stepE ← mkAppM lemmaConvertsM.name #[convertsME]
  let skipE ← mkAppM lemmaConverts.name #[convertsME, convertsM]
  let hypWFE ← Expr.mkDirectProjection convertsME `wellFormed
  let hypConstraintsE ← Expr.mkDirectProjection convertsME `constraints
  let (_, goal) ← goal.assertHypotheses #[
    ←Hypothesis.ofNameValue `this convertsME,
    ←Hypothesis.ofNameValue `h_mapM_result stepE,
    ←Hypothesis.ofNameValue `h_wellFormed hypWFE,
    ←Hypothesis.ofNameValue `h_constraints hypConstraintsE,
    ←Hypothesis.ofNameValue `h_idx skipE
  ]
  return goal

elab "step" convertsM:term "using" converts:ident : tactic => withMainContext do
  let convertsME ← elabTerm convertsM .none
  let convertsE := (←getLCtx).getFromUserName! converts.getId
  logInfo m!"Called `step` with arguments:\n{←elabTerm convertsM .none}\n{converts.getId}"
  liftMetaTactic' (step_impl convertsME convertsE.toExpr)

  -- liftMetaTactic' (step_impl convertsM.getId)
  -- evalTactic (←`(tactic|have $(mkIdent (.mkSimple "this")) := $convertsM))
  -- withMainContext do
  -- let typeOfConvertsM : Lean.Expr ←
  --   instantiateMVars <| (←getLCtx).getFromUserName! convertsM.getId |>.type
  -- -- have h_mapM_result := FList.converts_of_convertsM this
  -- --     have h_wellFormed := this.wellFormed
  -- --     have h_constraints1 := this.constraints
  -- match_expr typeOfConvertsM with
  -- | Clap.Lang.FList.ConvertsM _ _ _ _ =>
  --   logInfo m!"FList"
  -- | Clap.Lang.FArray.ConvertsM _ _ _ _ => logInfo m!"FArray"
  -- | Clap.Lang.FUnit.ConvertsM _ _ _ _ => logInfo m!"FUnit"
  -- | Clap.Lang.FB.ConvertsM _ _ _ _ => logInfo m!"FB"
  -- | Clap.Lang.F.ConvertsM _ _ _ _ => logInfo m!"F"
  -- | _ => logInfo m!"Your mother"

end

lemma convertsM_but_sane?
  {state}
  {len : ℕ}
  {idx : F}
  {idx_val : ZMod p} -- TODO : Fin len?
  (h_idx : F.Converts state idx idx_val)
  (h_len : len < p)
:
  FArray.ConvertsM (oneHotRaw len idx) state (Vector.ofFn (λ x => x.val == idx_val.val))
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

      -- Get ConvertsM for the mapM over the first len elements
      specialize h_len tl (by aesop (add safe (by grind))) (by grind)
      simp at h_len
      -- assert that our previous state still holds after the mapM
      have := h_len
      -- step this using h_idx
      have h_mapM_result := FList.converts_of_convertsM this
      have h_wellFormed := this.wellFormed
      have h_constraints1 := this.constraints
      apply F.converts_skip this at h_idx
      set mapM := List.mapM
          (fun i => do
            let idx_val ← liftM (HashConsM.mkConstant (i : ZMod p))
            eq (p := p) idx idx_val)
          tl.reverse
      set mapM_result := mapM.getResult state.numAlloc state.σ
      set state := mapM.getState state
      clear this

      -- Get ConvertsM for mkConstant and assert that previous state still holds
      have := @MkConstant.convertsM p state hd
      have h_a := F.converts_of_convertsM this
      have h_wellFormed := this.wellFormed
      have h_constraints2 := this.constraints
      apply F.converts_skip this at h_idx
      apply FList.converts_skip this at h_mapM_result
      set mkConst := (liftM (n := ClapM p) (HashConsM.mkConstant (p := p) (hd : ZMod p)))
      set c_result := mkConst.getResult state.numAlloc state.σ
      set state := mkConst.getState state
      clear this

      -- Get ConvertsM for eq and assert that previous state still holds
      have := eq.convertsM h_idx h_a
      have h_eq := FB.converts_of_convertsM this
      have h_wellFormed := this.wellFormed
      have h_constraints2 := this.constraints
      apply F.converts_skip this at h_idx
      apply FList.converts_skip this at h_mapM_result
      set eq := eq (p := p) idx c_result
      set eq_result := eq.getResult state.numAlloc state.σ
      set eq_state := eq.getState state
      clear this

      -- Apply the Functor map to the result of our eq, leaving the state unaffected
      have h_eq_map := FList.converts_append
        h_mapM_result
        (FList.converts_singleton_of_converts_FB h_eq)

      simp at *
          -- We've reached the end of the function, so strip away the boilerplate and prove
                -- that the canonical spec matches our hand written one


      -- We've reached the end of the function, so strip away the boilerplate and prove
      -- that the canonical spec matches our hand written one
      constructor
      . unfold FList.Converts at h_eq_map
        convert h_eq_map
        . grind [ClapM.getState]
        . grind [ClapM.getState]
        . -- Spec proof
          rewrite [←ZMod.val_cast_of_lt (a := hd) (not_this hd (by grind))]
          simp only [ZMod.val_natCast, beq_eq_beq]
          apply Iff.intro
          . intro h
            simp [h]
          . intro h
            simp [h]
      . grind
      . grind [ClapM.getState]

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
  (h_a : F.Converts state a val)
  (h_b : F.Converts state b val)
:
  FUnit.ConvertsM (assert_eq a b) state ()
:= by
  unfold assert_eq

  have := mkSub.convertsM h_a h_b
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  simp only [ClapM.map_wellFormed] at h_wf
  simp at this
  have := eq0.convertsM (F.converts_of_convertsM this)
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  unfold FUnit.ConvertsM at this
  constructor
  . convert this.result using 1
    . grind
    . grind
  . grind
  . grind [ClapM.getState]

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
  (h_vals : FArray.Converts state f_vals vals)
  (h_init : F.Converts state init 0)
:
  F.ConvertsM (f_vals.sum' init) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum
:= by
  unfold sum'

  induction' k with k h_k
  . have (init : ExprRef) : Vector.foldlM (λ x y => liftM (n := ClapM p) (HashConsM.mkAdd (p := p) x y)) init f_vals = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := f_vals
      grind
    simp [this]
    have : vals = #v[] := by grind
    simp [this]
    constructor
    . unfold F.Converts at h_init
      simp [ClapM.getState]
      grind [cases ClapMState]
    . grind
    . simp [ClapM.runAndEval]
  . have := (FArray.converts_cast (k2 := k) (FArray.converts_pop h_vals) (by trivial))
    set fvals_base := Vector.cast (m := k) (by trivial) f_vals.pop
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop

    have := @h_k fvals_base vals_base this
    have h_fvals_base := F.converts_of_convertsM this
    have h_wellFormed := this.wellFormed
    have h_constraints2 := this.constraints
    apply FArray.converts_skip this at h_vals
    set foldlM := Vector.foldlM (fun x y => liftM (n := ClapM p) (HashConsM.mkAdd (p := p) x y)) init fvals_base
    set foldl_result := foldlM.getResult state.numAlloc state.σ
    set state := foldlM.getState state
    simp at *
    clear this

    have : f_vals = fvals_base.push f_vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [fvals_base]
      . grind
    rewrite [this]
    simp [Vector.foldlM_push]

    have h_fvals_k := F.converts_of_FB_converts (FArray.converts_getElem h_vals (Nat.lt_succ_self k))

    have := mkAdd.convertsM h_fvals_base h_fvals_k
    have h_add := F.converts_of_convertsM this
    have h_wellFormed := this.wellFormed
    have h_constraints2 := this.constraints
    set add := liftM (n := ClapM p) (HashConsM.mkAdd (p := p) foldl_result f_vals[k])
    set add_result := add.getResult state.numAlloc state.σ
    set state := add.getState state
    simp at *
    clear this

    constructor
    . unfold F.Converts at h_add
      convert h_add
      . grind
      . grind [ClapM.getState]
      . have : vals = vals_base.push vals[k] := by
          ext
          rewrite [Vector.getElem_push]
          split
          . simp [vals_base]
          . grind
        rewrite [this]
        simp
    . grind
    . grind [ClapM.getState]

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
  (h_vals : FArray.Converts state f_vals vals)
:
  F.ConvertsM (f_vals.sum) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum
:= by
  unfold sum
  simp [←sum'.eq_def]

  have := @MkConstant.convertsM p state 0
  have h_zero := F.converts_of_convertsM this
  have h_wf := this.wellFormed
  have h_constraints := this.constraints
  apply FArray.converts_skip this at h_vals
  set mkZero := liftM (n := ClapM p) (HashConsM.mkConstant (p := p) 0)
  set mkZero_result := mkZero.getResult state.numAlloc state.σ
  set mkZero_state := mkZero.getState state
  simp at *

  have := sum'.convertsM h_vals h_zero
  have h_sum' := F.converts_of_convertsM this
  have h_wf := this.wellFormed
  have h_constraints := this.constraints

  constructor
  . unfold F.Converts at h_sum'
    convert h_sum'
    . grind
    . grind [ClapM.getState]
  . grind
  . grind [ClapM.getState]

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
  (h_idx : F.Converts state idx idx_val)
  (h_len : len < p)
  (h_idx_val : idx_val.val < len)
:
  FArray.ConvertsM (singleOneArray len idx) state (Vector.ofFn (λ x => x.val == idx_val.val))
:= by
  unfold singleOneArray

  have := oneHotRaw.convertsM_but_sane? h_idx h_len
  have h_oneHot := FArray.converts_of_convertsM this
  have h_wellFormed := this.wellFormed
  have h_constraints2 := this.constraints
  apply F.converts_skip this at h_idx
  simp [-toList_map_oneHotRaw_eq_oneHotRaw'] at *
  set result := (oneHotRaw len idx).getResult state.numAlloc state.σ
  set state := (oneHotRaw len idx).getState state
  clear this

  have := FArray.sum.convertsM h_oneHot
  have h_sum := F.converts_of_convertsM this
  have h_wellFormed := this.wellFormed
  have h_constraints2 := this.constraints
  apply F.converts_skip this at h_idx
  apply FArray.converts_skip this at h_oneHot
  simp at *
  set sum := result.sum.getResult state.numAlloc state.σ
  set state := result.sum.getState state
  clear this

  have := @MkConstant.convertsM p state 1
  have h_one := F.converts_of_convertsM this
  have h_wellFormed := this.wellFormed
  have h_constraints2 := this.constraints
  apply F.converts_skip this at h_idx
  apply FArray.converts_skip this at h_oneHot
  apply F.converts_skip this at h_sum
  simp at h_idx h_oneHot h_sum
  set mkOne := liftM (n := ClapM p) (HashConsM.mkConstant (p := p) 1)
  set one := mkOne.getResult state.numAlloc state.σ
  set state := mkOne.getState state
  clear this

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

  have h_sum : F.Converts state sum 1 := by
    convert h_sum
    rw [this]

  have := assert_eq.convertsM h_sum h_one
  have h_wellFormed := this.wellFormed
  have h_constraints2 := this.constraints
  apply F.converts_skip this at h_idx
  apply FArray.converts_skip this at h_oneHot
  apply F.converts_skip this at h_sum
  apply F.converts_skip this at h_one
  simp at h_idx h_oneHot h_sum h_one
  set assert := assert_eq sum one
  set assert_result := assert.getResult state.numAlloc state.σ
  set state := assert.getState state
  clear this

  constructor
  . unfold FArray.Converts at h_oneHot
    convert h_oneHot
    . grind
    . grind
  . grind
  . grind [ClapM.getState]



end singleOneArray

end singleOneArray




end Clap.Lang
