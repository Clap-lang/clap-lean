import Clap.eDSLState.Convert.Base
import Clap.eDSLState.HashCons.HashConsM

import Clap.Lang.Wheels
import Clap.Lang.F.Tactics

namespace Clap.Lang

variable {p : ℕ}

section User

abbrev F (p : ℕ) : Type := HashConsM.BoundRef p
abbrev FB (p : ℕ) : Type := F p
abbrev FArray (p k : ℕ) : Type := Vector (FB p) k
abbrev FList (p : ℕ) : Type := List (FB p)

section OverrideInstance

open HashConsM in
instance : HAdd (F p) (F p) (ClapM p (F p)) :=
  inferInstanceAs (HAdd (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

open HashConsM in
instance : HSub (F p) (F p) (ClapM p (F p)) :=
  inferInstanceAs (HSub (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

open HashConsM in
instance : HMul (F p) (F p) (ClapM p (F p)) :=
  inferInstanceAs (HMul (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

open HashConsM in
instance : HAdd (FB p) (FB p) (ClapM p (FB p)) :=
  inferInstanceAs (HAdd (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

open HashConsM in
instance : HSub (FB p) (FB p) (ClapM p (FB p)) :=
  inferInstanceAs (HSub (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

open HashConsM in
instance : HMul (FB p) (FB p) (ClapM p (FB p)) :=
  inferInstanceAs (HMul (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)))

end OverrideInstance

end User

section Converts

namespace F

abbrev conversion : Conversion p (F p) where
  IdealT := ZMod p
  toExprs x := [x]
  conversion x := [x]

end F


namespace FB

abbrev conversion : Conversion p (FB p) where
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

abbrev conversion {k} : Conversion p (FArray p k) where
  IdealT := Vector Bool k
  toExprs x := x.toList
  conversion x := (x.map fun x ↦ if x then 1 else 0).toList

end FArray


namespace FList

abbrev conversion : Conversion p (FList p) where
  IdealT := List Bool
  toExprs x := x
  conversion x := x.map fun x ↦ if x then 1 else 0

end FList

end Converts


section ConvertsLemmas

namespace F

lemma converts_of_FB_converts
  {state : ClapMState p}
  {expr : FB p}
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
  {expr : F p}
  {val}
  (h : Converts F.conversion state expr val)
  (h_val : val.val < 2)
:
  Converts FB.conversion state (expr : FB p) (val == 1)
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

lemma convertsM_of_F_convertsM
  [p.AtLeastTwo]
  {action : ClapM p (F p)}
  {state : ClapMState p}
  {val : ZMod p}
  {constraints}
  (h : ConvertsM F.conversion action state val constraints)
  (h_val : val.val < 2)
:
  ConvertsM FB.conversion action state (val == 1) constraints
:= by
  constructor
  . exact converts_of_F_converts h.result h_val
  . exact h.wellFormed
  . exact h.constraints

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
  {exprs : FArray p k}
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
  {exprs : Vector (FB p) k}
  {expr : FB p}
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
  {action : ClapM p (Vector (FB p) k)}
  {state}
  {val : Vector Bool k}
  {constraints}
  (h : ConvertsM FList.conversion (Vector.toList <$> action) state val.toList constraints)
:
  ConvertsM conversion action state val constraints
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
  {exprs : FArray p k1}
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
  {exprs : FArray p k}
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
  {exprs : FArray p k}
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
  {exprs1 exprs2 : List (FB p)}
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

end Clap.Lang
