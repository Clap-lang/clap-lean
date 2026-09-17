import Clap.eDSLState.Convert.Base
import Clap.eDSLState.HashCons.HashConsM

import Clap.Lang.Wheels
import Clap.Lang.F.Tactics

namespace Clap.Lang

variable {p : ℕ}

section User

abbrev F (p : ℕ) : Type := HashConsM.BoundRef p
abbrev FB (p : ℕ) : Type := F p
abbrev F8 (p : ℕ) : Type := F p
abbrev FArray (p k : ℕ) : Type := Vector (FB p) k
abbrev FBitVec (p k : ℕ) : Type := Vector (FB p) k
abbrev FList (p : ℕ) : Type := List (FB p)
/-- A vector of arbitrary field elements. Same underlying type as `FArray p k`; the two differ
only in which `Conversion` you cite, `FVec.conversion` (`Vector (ZMod p) k`) or
`FArray.conversion` (`Vector Bool k`). -/
abbrev FVec (p k : ℕ) : Type := Vector (F p) k

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

namespace F8

abbrev conversion : Conversion p (F8 p) where
  IdealT := UInt8
  toExprs x := [x]
  conversion x := [(x.toNat : ZMod p)]

end F8

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


namespace FVec

abbrev conversion {k} : Conversion p (FVec p k) where
  IdealT := Vector (ZMod p) k
  toExprs x := x.toList
  conversion x := x.toList

end FVec


-- A pair of field elements, so that a fold over `a.zip b` has an element conversion.
namespace FPair

abbrev conversion : Conversion p (F p × F p) where
  IdealT := ZMod p × ZMod p
  toExprs x := [x.1, x.2]
  conversion x := [x.1, x.2]

end FPair

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

lemma converts_of_F8_converts
  {state : ClapMState p}
  {expr : F8 p}
  {u : UInt8}
  (h : Converts F8.conversion state expr u)
:
  Converts F.conversion state expr (u.toNat : ZMod p)
:= converts_cast
  (conversion1 := F8.conversion)
  (conversion2 := F.conversion)
  (y := expr)
  (val2 := (u.toNat : ZMod p))
  h (by rfl) (by rfl)

end F

namespace FB

lemma converts_of_F_converts
  [NeZero p]
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
      have h_ne : val ≠ 1 := by simpa using h_neq
      have h01 : val.val = 0 ∨ val.val = 1 := by omega
      rcases h01 with h0 | h1
      . exact (ZMod.val_eq_zero val).mp h0
      . exfalso
        apply h_ne
        have h_round := ZMod.natCast_rightInverse (n := p) val
        rw [h1] at h_round
        simpa using h_round.symm

/-- A field element known to be `0` is the bit `false`. -/
lemma converts_zero
  [p.AtLeastTwo]
  {state : ClapMState p}
  {expr : F p}
  (h : Converts F.conversion state expr 0)
:
  Converts FB.conversion state expr false
:= by
  haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
  have h01 : ((0 : ZMod p) == 1) = false := beq_eq_false_iff_ne.mpr zero_ne_one
  rw [← h01]
  exact converts_of_F_converts h (by simp)

/-- A field element known to be `1` is the bit `true`. -/
lemma converts_one
  [p.AtLeastTwo]
  {state : ClapMState p}
  {expr : F p}
  (h : Converts F.conversion state expr 1)
:
  Converts FB.conversion state expr true
:= by
  haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
  have h11 : ((1 : ZMod p) == 1) = true := beq_self_eq_true 1
  rw [← h11]
  refine converts_of_F_converts h ?_
  have := ZMod.val_one_le_one (n := p)
  omega

lemma convertsM_of_F_convertsM
  [NeZero p]
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

namespace F8

lemma converts_of_F_converts
  [NeZero p]
  {state : ClapMState p}
  {expr : F p}
  {val}
  (h : Converts F.conversion state expr val)
  (h_val : val.val < UInt8.size)
:
  Converts F8.conversion state (expr : F8 p) (UInt8.ofNat val.val)
:= by
  apply converts_cast h
  . rfl
  . unfold F.conversion conversion
    simp
    rw [Nat.mod_eq_of_lt h_val]
    exact (ZMod.natCast_rightInverse (n := p) val).symm

lemma convertsM_of_F_convertsM
  [NeZero p]
  {action : ClapM p (F p)}
  {state : ClapMState p}
  {val : ZMod p}
  {constraints}
  (h : ConvertsM F.conversion action state val constraints)
  (h_val : val.val < UInt8.size)
:
  ConvertsM F8.conversion action state (UInt8.ofNat val.val) constraints
:= by
  constructor
  . exact converts_of_F_converts h.result h_val
  . exact h.wellFormed
  . exact h.constraints

end F8

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

lemma converts_append
  {k1 k2}
  {state : ClapMState p}
  {exprs1 : FArray p k1}
  {exprs2 : FArray p k2}
  {vals1 : Vector Bool k1}
  {vals2 : Vector Bool k2}
  (h_exprs1 : Converts conversion state exprs1 vals1)
  (h_exprs2 : Converts conversion state exprs2 vals2)
:
  Converts conversion state (exprs1 ++ exprs2) (vals1 ++ vals2)
:= by
  rewrite [converts_iff_FB_converts] at h_exprs1 h_exprs2 ⊢
  intro ⟨i, h_i⟩
  by_cases h : i < k1
  . convert (h_exprs1 ⟨i, h⟩) using 1
    . grind
    . grind
  . convert (h_exprs2 ⟨i - k1, by grind⟩) using 1
    . grind
    . grind

lemma converts_replicate
  {k}
  {state : ClapMState p}
  {expr : FB p}
  {val : Bool}
  (h : Converts FB.conversion state expr val)
:
  Converts conversion state (Vector.replicate k expr) (Vector.replicate k val)
:= by
  rewrite [converts_iff_FB_converts]
  intro ⟨i, h_i⟩
  convert h using 1 <;> simp

lemma converts_reverse
  {k}
  {state : ClapMState p}
  {exprs : FArray p k}
  {vals : Vector Bool k}
  (h : Converts conversion state exprs vals)
:
  Converts conversion state exprs.reverse vals.reverse
:= by
  rewrite [converts_iff_FB_converts] at ⊢ h
  intro ⟨i, h_i⟩
  convert (h ⟨k - 1 - i, by grind⟩) using 1
  . grind
  . grind

lemma converts_ofFn
  {k}
  {state : ClapMState p}
  {f : Fin k → FB p}
  {g : Fin k → Bool}
  (h : ∀ i : Fin k, Converts FB.conversion state (f i) (g i))
:
  Converts conversion state (Vector.ofFn f) (Vector.ofFn g)
:= by
  rewrite [converts_iff_FB_converts]
  intro ⟨i, h_i⟩
  convert h ⟨i, h_i⟩ using 1 <;> simp

lemma converts_tail
  {k}
  {state : ClapMState p}
  {exprs : FArray p k}
  {val : Vector Bool k}
  (h : Converts conversion state exprs val)
:
  Converts conversion state (exprs.tail) (val.tail)
:= by
  rewrite [converts_iff_FB_converts] at ⊢ h
  intro ⟨i, h_i⟩
  have h_i' : i + 1 < k := by grind
  convert (h ⟨i + 1, h_i'⟩) using 1
  . simp; congr 1; omega
  . simp; congr 1; omega

end FArray


namespace FPair

lemma converts_intro
  {state : ClapMState p}
  {x y : F p}
  {xv yv : ZMod p}
  (h_x : Converts F.conversion state x xv)
  (h_y : Converts F.conversion state y yv)
:
  Converts conversion state (x, y) (xv, yv)
:= by
  obtain ⟨_, x_varSet, x_wf, x_val⟩ := h_x
  obtain ⟨_, y_varSet, y_wf, y_val⟩ := h_y
  simp at x_varSet x_wf x_val y_varSet y_wf y_val
  refine ⟨by simp, ?_, ?_, ?_⟩ <;>
  · intro ⟨ib, h_ib⟩
    simp at h_ib ⊢
    interval_cases ib <;> simp [*]

lemma converts_fst
  {state : ClapMState p}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (h : Converts conversion state xy xy_val)
:
  Converts F.conversion state xy.1 xy_val.1
:= by
  have v0 := h.varSet_wf ⟨0, by simp⟩
  have w0 := h.expr_wf ⟨0, by simp⟩
  have a0 := h.value_eq ⟨0, by simp⟩
  simp at v0 w0 a0
  exact ⟨by simp, fun _ ↦ by simpa using v0, fun _ ↦ by simpa using w0,
         fun _ ↦ by simpa using a0⟩

lemma converts_snd
  {state : ClapMState p}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (h : Converts conversion state xy xy_val)
:
  Converts F.conversion state xy.2 xy_val.2
:= by
  have v1 := h.varSet_wf ⟨1, by simp⟩
  have w1 := h.expr_wf ⟨1, by simp⟩
  have a1 := h.value_eq ⟨1, by simp⟩
  simp at v1 w1 a1
  exact ⟨by simp, fun _ ↦ by simpa using v1, fun _ ↦ by simpa using w1,
         fun _ ↦ by simpa using a1⟩

end FPair


namespace FVec

@[simp]
lemma converts_empty
  {state : ClapMState p}
:
  Converts conversion state #v[] #v[]
:= by
  constructor <;> grind

lemma converts_iff_F_converts
  {k}
  {state : ClapMState p}
  {exprs : FVec p k}
  {val : Vector (ZMod p) k}
:
  Converts conversion state exprs val ↔
  (∀ i : Fin k, Converts F.conversion state exprs[i] val[i])
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

lemma converts_getElem
  {k i}
  {state : ClapMState p}
  {exprs : FVec p k}
  {vals : Vector (ZMod p) k}
  (h : Converts conversion state exprs vals)
  (h_i : i < k)
:
  Converts F.conversion state exprs[i] vals[i]
:= (converts_iff_F_converts.mp h) ⟨i, h_i⟩

lemma converts_push
  {k}
  {state : ClapMState p}
  {exprs : FVec p k}
  {expr : F p}
  {vals : Vector (ZMod p) k}
  {val : ZMod p}
  (h_exprs : Converts conversion state exprs vals)
  (h_expr : Converts F.conversion state expr val)
:
  Converts conversion state (exprs.push expr) (vals.push val)
:= by
  rewrite [converts_iff_F_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  by_cases i = k
  . convert h_expr
    . grind
    . grind
  . convert (h_exprs ⟨i, by grind⟩) using 1
    . grind
    . grind

lemma converts_pop
  {k}
  {state : ClapMState p}
  {exprs : FVec p k}
  {val : Vector (ZMod p) k}
  (h : Converts conversion state exprs val)
:
  Converts conversion state (exprs.pop) (val.pop)
:= by
  rewrite [converts_iff_F_converts] at ⊢ h
  intro ⟨i, h_i⟩
  convert (h ⟨i, by grind⟩) using 1
  . grind
  . grind

lemma converts_vector_cast
  {k1 k2}
  {state : ClapMState p}
  {exprs : FVec p k1}
  {val : Vector (ZMod p) k1}
  (h : Converts conversion state exprs val)
  (h_k : k1 = k2)
:
  Converts conversion state (exprs.cast h_k) (val.cast h_k)
:= by
  rewrite [converts_iff_F_converts] at ⊢ h
  intro ⟨i, h_i⟩
  exact h ⟨i, by grind⟩

lemma converts_append
  {k1 k2}
  {state : ClapMState p}
  {exprs1 : FVec p k1}
  {exprs2 : FVec p k2}
  {vals1 : Vector (ZMod p) k1}
  {vals2 : Vector (ZMod p) k2}
  (h_exprs1 : Converts conversion state exprs1 vals1)
  (h_exprs2 : Converts conversion state exprs2 vals2)
:
  Converts conversion state (exprs1 ++ exprs2) (vals1 ++ vals2)
:= by
  rewrite [converts_iff_F_converts] at h_exprs1 h_exprs2 ⊢
  intro ⟨i, h_i⟩
  by_cases h : i < k1
  . convert (h_exprs1 ⟨i, h⟩) using 1
    . grind
    . grind
  . convert (h_exprs2 ⟨i - k1, by grind⟩) using 1
    . grind
    . grind

lemma converts_reverse
  {k}
  {state : ClapMState p}
  {exprs : FVec p k}
  {vals : Vector (ZMod p) k}
  (h : Converts conversion state exprs vals)
:
  Converts conversion state exprs.reverse vals.reverse
:= by
  rewrite [converts_iff_F_converts] at ⊢ h
  intro ⟨i, h_i⟩
  convert (h ⟨k - 1 - i, by grind⟩) using 1
  . grind
  . grind

/-- Element-wise view of `a.zip b`, the shape every two-vector fold needs. -/
lemma converts_zip
  {k i}
  {state : ClapMState p}
  {a b : FVec p k}
  {a_vals b_vals : Vector (ZMod p) k}
  (h_a : Converts conversion state a a_vals)
  (h_b : Converts conversion state b b_vals)
  (h_i : i < k)
:
  Converts FPair.conversion state (a.zip b)[i] ((a_vals.zip b_vals)[i])
:= by
  have h := FPair.converts_intro (converts_getElem h_a h_i) (converts_getElem h_b h_i)
  convert h using 2 <;> grind

/-- Every `FArray` (bit vector) is an `FVec` whose ideal values are the bits' field images. -/
lemma converts_of_FArray_converts
  {k}
  {state : ClapMState p}
  {exprs : FArray p k}
  {vals : Vector Bool k}
  (h : Converts FArray.conversion state exprs vals)
:
  Converts conversion state exprs (vals.map (fun b ↦ if b then (1 : ZMod p) else 0))
:= by
  rewrite [converts_iff_F_converts]
  rewrite [FArray.converts_iff_FB_converts] at h
  intro ⟨i, h_i⟩
  convert F.converts_of_FB_converts (h ⟨i, h_i⟩) using 1
  simp

end FVec


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
