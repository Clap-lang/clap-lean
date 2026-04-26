import Clap.Primes
import Clap.Spec
import Clap.BitVec
import Clap.Lang
import Clap.Compiler.Basic

open Clap.Lang Clap.Lang.ZMod
abbrev p := Primes.goldilocks
open Core

namespace ExampleIsZero

def F.ofBool (x : Bool) : F p := if x then 1 else 0

def spec (v : Vector (F p) 2) (expected : F p) : Prop :=
  let expected_bool := v.all (fun x ↦ x = 0)
  expected = F.ofBool expected_bool

def impl (v : Vector (F p) 2) (expected : F p) : Option Unit := do
  let prod ← v.foldlM (fun acc x ↦ FB.and acc <$> isZero x) FB.true
  F.assertEq prod expected

lemma lr (v : Vector (F p) 2) (expected : F p) :
  spec v expected → impl v expected = some () := by
  unfold spec impl
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  aesop (add simp [sub_eq_zero, mul_comm,eq0,isZero,instCoreZMod,Clap.Spec.Compiler.eq0,Clap.Spec.Compiler.isZero,F.assertEq,FB.and,F.ofBool])

lemma rl (v : Vector (F p) 2) (expected : F p) :
  impl v expected = some () → spec v expected := by
  unfold spec impl
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  aesop (add simp [sub_eq_zero, mul_comm,eq0,isZero,instCoreZMod,Clap.Spec.Compiler.eq0,Clap.Spec.Compiler.isZero,F.assertEq,FB.and,F.ofBool])

lemma equiv (v : Vector (F p) 2) (expected : F p) :
  impl v expected = some () ↔ spec v expected := by
  aesop (add simp [lr,rl])

def ex_reduced (v : Vector (F p) 2)
               (expected : F p) : Option Unit := do
  let z0 ← isZero v[0]
  let z1 ← isZero v[1]
  eq0 (z0 * z1 - expected)

def ex_cs (v : Vector (F p) 2)
          (expected : F p) : F p → F p → F p → F p → Option Unit :=
  fun inv0 z0 inv1 z1 ↦ do
  eq0 ((1:F p) - inv0 * v[0] - z0)
  eq0 (z0 * v[0])
  eq0 ((1:F p) - inv1 * v[1] - z1)
  eq0 (z1 * v[1])
  eq0 (z0 * z1 - expected)

def ex_wg (v : Vector (ZMod p) 2)
          (expected : ZMod p) : List (ZMod p) :=
  let z0 := if v[0] = 0 then 1 else 0
  let inv0 := v[0]⁻¹
  .cons z0 (.cons inv0 (
  let z1 := if v[1] = 0 then 1 else 0
  let inv1 := v[1]⁻¹
  .cons z1 (.cons inv1 (
  []
  ))))

end ExampleIsZero

namespace ExampleShare

def spec (v : Vector (F p) 2) (expected : F p) : Prop :=
  v.foldl (fun acc x ↦ acc * x) 1 = expected

def circuit (v : Vector (F p) 2) (expected : F p) : Option Unit := do
  let prod ← v.foldlM (fun prod x ↦ share (x * prod)) 1
  F.assertEq prod expected

lemma lr (v : Vector (F p) 2) (expected : F p) :
  spec v expected → circuit v expected = some () := by
  unfold spec circuit
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  aesop (add simp [sub_eq_zero, mul_comm,eq0,share,instCoreZMod,Clap.Spec.Compiler.eq0,Clap.Spec.Compiler.share,F.assertEq])

lemma rl (v : Vector (F p) 2) (expected : F p) :
  circuit v expected = some () → spec v expected := by
  unfold spec circuit
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  aesop (add simp [sub_eq_zero, mul_comm,eq0,share,instCoreZMod,Clap.Spec.Compiler.eq0,Clap.Spec.Compiler.share,F.assertEq])

lemma equiv (v : Vector (F p) 2) (expected : F p) :
  circuit v expected = some () ↔ spec v expected := by
  aesop (add simp [lr,rl])

def circuit_reduced (v : Vector (F p) 2)
                    (expected : F p) : Option Unit := do
  let prod0 ← share (v[0] * 1)
  let prod  ← share (v[1] * prod0)
  eq0 (prod - expected)

def ex_circuit_inlined (v : Vector (F p) 2)
                       (expected : F p) : Option Unit := do
  eq0 (v[1] * v[0] - expected)

def ex_cs (v : Vector (F p) 2)
          (expected : F p) : F p → F p → Option Unit :=
  fun prod0 prod ↦ do
  eq0 (v[0] * 1 - prod0)
  eq0 (v[1] * prod0 - prod)
  eq0 (prod - expected)

def ex_wg (v : Vector (ZMod p) 2)
          (expected : ZMod p) : List (ZMod p) :=
  let prod0 := v[0] * 1
  .cons prod0 (
  let prod := v[1] * prod0
  .cons prod (
  []))

end ExampleShare

namespace ExampleEq0

def impl (v : Vector (F p) 2) : Option Unit :=
  Vector.foldlM (fun () x ↦ eq0 x) () v

def spec {n} (v : Vector (F p) n) : Prop := ∀ e ∈ v, e = 0

lemma lr (v : Vector (F p) 2) : spec v → impl v = some () := by
  simp [impl,spec]
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  intro h
  rw [Vector.foldlM_mk]
  aesop (add simp [eq0,instCoreZMod,Clap.Spec.Compiler.eq0])

lemma rl (v : Vector (F p) 2) : impl v = some () → spec v := by
  simp [impl,spec]
  have hv : v = #v[v[0],v[1]] := by
    rcases v with ⟨⟨_ | ⟨v0 , (_ | ⟨v1 , (_ | ⟨_, _⟩)⟩)⟩⟩,h⟩ <;> aesop
  rw [hv]
  rw [Vector.foldlM_mk]
  aesop (add simp [eq0,instCoreZMod,Clap.Spec.Compiler.eq0])

lemma equiv (v : Vector (F p) 2) : impl v = some () ↔ spec v := by
  aesop (add simp [lr, rl])

end ExampleEq0

def circuit (v : Vector (F p) 3) (expected : F p) : Option Unit := do
  let allZero ← v.foldlM (fun acc x ↦ do FB.and acc (←isZero x)) (1:F p)
  F.assertEq allZero expected

example : circuit #v[0,0,0] 1 = some () := by native_decide

def reduced (v : Vector (F p) 3) (expected : F p) : Option Unit := do
  let z0 ← isZero v[0]
  let acc := 1 * z0
  let z1 ← isZero v[1]
  let acc := z1 * acc
  let z2 ← isZero v[2]
  let acc := z2 * acc
  eq0 (acc - expected)

example : circuit = reduced := by
  unfold circuit reduced F.assertEq FB.and
  funext v exp
  have h : v = #v[v[0],v[1],v[2]] := by
    aesop (add safe cases [Vector, Array, List])
  rw [h]
  simp [Option.bind_assoc,Option.bind_some]
  congr
  funext
  congr
  funext
  congr
  funext
  congr 2
  grind
