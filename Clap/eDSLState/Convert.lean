-- import Clap.eDSLState.IsValid

-- namespace Clap

-- class Convert (p : ℕ) (representsT idealT : Type) extends IsValid p representsT where
--   toIdeal : (VarStore p) → (HashConsSt p) → representsT → Option idealT
--   toRepresents : idealT → HashConsM p representsT
--   isValid_iff_isSome_toIdeal :
--     ∀ (varStore : VarStore p) (σ : HashConsSt p) (x : representsT),
--       isValid varStore σ x ↔ (toIdeal varStore σ x).isSome
--   toIdeal_toRepresents :
--     ∀ (varStore : VarStore p) (σ : HashConsSt p) (x : idealT),
--       toIdeal varStore ((toRepresents x).getHashConsState σ) ((toRepresents x).getResult σ) = .some x

-- @[simp, grind =]
-- lemma Convert.toRepresents_toIdeal
--   {p : ℕ}
--   {representsT idealT : Type}
--   [inst: Convert p representsT idealT]
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   {x : representsT}
--   (h : IsValid.isValid varStore σ x)
-- :
--   toIdeal (representsT := representsT) (idealT := idealT) varStore σ
--     ((toRepresents (representsT := representsT) ((toIdeal (idealT := idealT) varStore σ x).get ((isValid_iff_isSome_toIdeal varStore σ x).mp h))).getResult σ) =
--   inst.toIdeal varStore σ x
-- := by
--   have := inst.toIdeal_toRepresents
--   simp [HashConsM.getHashConsState, HashConsM.getResult] at this ⊢

--   simp [inst.toIdeal_toRepresents]

-- instance {p : ℕ} : Convert p Unit Unit where
--   isValid := fun _ _ _ ↦ True
--   toIdeal _ x := .some x
--   toRepresents x := x
--   isValid_iff_isSome_toIdeal _ _ := by grind
--   toIdeal_toRepresents _ _ := by grind

-- @[simp, grind .]
-- lemma isValid_iff_isSome_toIdeal {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {σ : HashConsSt p} {x : α}
-- :
--   (Convert.toIdeal (idealT := β) varStore x).isSome ↔
--   IsValid.isValid varStore σ x
-- := by
--   aesop (add safe cases Convert)

-- @[grind .]
-- lemma isValid_of_toIdeal_eq_some {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {x : α} {b : β}
--   (h : (Convert.toIdeal (idealT := β) varStore x) = .some b)
-- :
--   IsValid.isValid varStore x
-- := by
--   have := Option.isSome_of_eq_some h
--   grind

-- @[simp, grind .]
-- lemma toIdealtoRepresents_of_convert {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {x : β}
-- :
--   Convert.toIdeal (representsT := α) varStore (Convert.toRepresents p x) = .some x
-- := by
--   aesop (add safe cases Convert)

-- end Clap
