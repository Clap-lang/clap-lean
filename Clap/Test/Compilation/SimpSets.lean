import Clap.Compiler.Wheels
import Clap.Poseidon.Poseidon

/-
Wheels.
-/

dsimproc_decl _root_.List.reduceRange (List.range _) := fun e ↦ do
  let_expr List.range k ← e | return .continue
  let l := List.range k.nat?.get!
  return .visit (Lean.toExpr l)

attribute [simproc] _root_.List.reduceRange

/-
Poseidon.
-/

-- open Clap.Poseidon.Constant.C Clap.Poseidon.Constant Clap.Poseidon.Constant.M Clap.Poseidon.Constant.P Clap.Poseidon.Constant.S Clap.Poseidon
-- attribute [simpPoseidon] 
--   C02 C03 C04 C05 C06 C07 C08 C09 C10 C11 C12 C13 C14 C15 C16 C17 C M P S
--   M02 M03 M04 M05 M06 M07 M08 M09 M10 M11 M12 M13 M14 M15 M16 M17 P02 P03
--   P04 P05 P06 P07 P08 P09 P10 P11 P12 P13 P14 P15 P16 P17 S02 S03 S04 S05
--   S06 S07 S08 S09 S10 S11 S12 S13 S14 S15 S16 S17

--   sigma ark mix mixLast poseidonEx poseidon liftArr liftMat poseidonBN254 p mixS

-- /-
-- Poseidon.mixS.
-- -/

-- attribute [simpMixS]
--   p mixS.dotProduct mixS.tail

/-
Synthetic.
-/

attribute [simpSynthetic]
  List.reduceRange List.pure_def List.bind_eq_flatMap List.flatMap_cons Nat.cast_zero
  Nat.cast_one Nat.cast_ofNat List.flatMap_nil List.append_nil List.cons_append List.nil_append
  List.foldlM_cons List.foldlM Option.pure_def Option.bind_eq_bind Option.bind_fun_some
  repeatN_inner
