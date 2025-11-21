import Mathlib.Data.ZMod.Basic
-- import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic -- field operations
-- import Mathlib.Algebra.Field.Defs  -- Add this!
-- import Mathlib.Algebra.Field.Basic  -- Field typeclass instances
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum -- norm_num

set_option autoImplicit false
set_option linter.unusedVariables true

-- variable (p : Nat)
-- variable [Fact (Nat.Prime p)]

def p : Nat := 7
abbrev F := ZMod p
instance : Fact (Nat.Prime p) := ⟨by decide⟩

example : (6 : F) / (2 : F) = 3 := by native_decide

-- Inverse (requires prime)
example : (3 : F)⁻¹ = 5 := by native_decide -- 3 * 5 = 15 ≡ 1 (mod 7)
example : (2 : F)⁻¹ = 4 := by native_decide -- 2 * 4 = 8 ≡ 1 (mod 7)

-- note that Fin n ~ ZMod n for n≠0
/-
theorem bla1 : ∀ (i:Nat), i < 4 -> i = ((OfNat.ofNat i):Fin 4).val := by intros ; simp ; unfold OfNat.ofNat instOfNatNat; simp ; grind

theorem bla2 : ∀ (i:Nat), i = ((OfNat.ofNat i):Fin 4).val := by intros ; simp ; unfold OfNat.ofNat instOfNatNat; simp ; grind

#eval ((OfNat.ofNat 6):F) -- 6
#eval ((OfNat.ofNat 7):F) -- 0
#eval (6:F) -- 6
#eval (7:F) -- 0
#eval (6=(6:F)) -- true
#eval (7=(7:F)) -- true ??
-/

-- TODO we need to enforce the range of each felt
def decomp (e:F) : Vector F 2 :=
  let e0 := e % 2
  let e1 := e / 2
  ⟨#[e0,e1],rfl⟩

def comp (v:Vector F 2) : F :=
  (v[0] + 2 * v[1])

-- // horner
-- let rec combine_spec (bits:list felt) : felt =
--   match bits with
--   | [] -> 0
--   | bit::bits -> Base.(bit +% 2 *% (combine_spec bits))

theorem decomp_comp : ∀ (e:F), (comp (decomp e)) = e := by
  intro x
  unfold comp decomp
  simp
  grind

namespace Hoas

inductive Exp where
  | c : F -> Exp
  | add : Exp -> Exp -> Exp
  | mul : Exp -> Exp -> Exp
  | sub : Exp -> Exp -> Exp

instance : Add Exp where
  add a b := .add a b

instance : Mul Exp where
  mul a b := .mul a b

instance : Sub Exp where
  sub a b := .sub a b

def eval_e (e: Exp) : F :=
  match e with
  | .c i => i
  | l + r => eval_e l + eval_e r
  | l * r => eval_e l * eval_e r
  | .sub l r => eval_e l - eval_e r

instance : Coe Exp F where
  coe := eval_e

instance : Coe F Exp where
  coe := .c

instance (n:Nat) : OfNat Exp n where
  ofNat := (↑n:F)

-- here we can add more types

inductive Circuit where
  | nil : Circuit
  | eq0 : Exp -> Circuit -> Circuit
  | lam : (Exp -> Circuit) -> Circuit
  | share : Exp -> (Exp -> Circuit) -> Circuit
  | inv : Exp -> (Exp -> Circuit) -> Circuit
  | is_zero : Exp -> (Exp -> Circuit) -> Circuit
  | assert_bool : Exp -> Circuit -> Circuit
  | assert_limb : Exp -> Circuit -> Circuit

-- tried to remove this using an index and subtype, did not work
inductive Cs where
  | nil : Cs
  | eq0 : Exp -> Cs -> Cs
  | lam : (Exp -> Cs) -> Cs

-- do we need to prove additional properties of this semantics?

namespace Functional
namespace Circuit

inductive Value where
  | false : Value
  | true : Value
  | abs : (Exp -> Circuit) -> Value

def eval (c:Circuit) : Value :=
  match c with
  | .nil => .true
  | .lam k => .abs k
  | .eq0 e c =>
    if eval_e e = 0 then eval c else .false
  | .share e k => eval (k (eval_e e))
  | .inv e k =>
    if eval_e e = 0
    then .false
    else eval (k (.c (1 / e)))
  | .is_zero e k =>
    if eval_e e = 0 then eval (k 1) else eval (k 0)
  | .assert_bool e c =>
    let e := eval_e e
    if e ∈ [0,1] then eval c else .false
  | .assert_limb e c =>
    let e := eval_e e
    if e.val < 4 then eval c else .false -- TODO is it ok to use < ?

inductive s_bisim : (l r: Value) -> Prop where
  | none
      : s_bisim .false .false
  | same
      : s_bisim .true .true
  | lam
      (kl kr:Exp -> Circuit)
      (h: ∀ x, s_bisim (eval (kl x)) (eval (kr x)))
      : s_bisim (.abs kl) (.abs kr)

theorem same : ∀ (c:Circuit), s_bisim (eval c) (eval c) := by
  intros c
  induction c with
  | lam k h =>
    simp [eval]
    constructor
    exact h
  | nil
  | _ _ _ h =>
    simp [eval] ; first | constructor | apply h | (split ; repeat (first | apply h | constructor))

end Circuit

namespace Cs

inductive Value where
  | false : Value
  | true : Value
  | abs : (Exp -> Cs) -> Value

def eval (cs:Cs) : Value :=
  match cs with
  | Cs.nil => .true
  | Cs.lam k => .abs k
  | Cs.eq0 e cs =>
    if eval_e e = 0 then eval cs else .false

inductive s_bisim : (l: Circuit.Value) -> (r: Value) -> Prop where
  | none
      : s_bisim .false .false
  | same
      : s_bisim .true .true
  | lam
      (kl:Exp -> Circuit)
      (kr:Exp -> Cs)
      (h: ∀ x, s_bisim (Circuit.eval (kl x)) (eval (kr x)))
      : s_bisim (.abs kl) (.abs kr)

inductive rw_bisim : (l: Circuit.Value) -> (r: Value) -> Prop where
  | none
      (l:Circuit.Value)
      : rw_bisim l .false
  | same
      : rw_bisim .true .true
  | lam
      (kl:Exp -> Circuit)
      (kr:Exp -> Cs)
      (h: ∀ x, rw_bisim (Circuit.eval (kl x)) (eval (kr x)))
      : rw_bisim (.abs kl) (.abs kr)
  | async
      (l:Circuit.Value)
      (kr:Exp -> Cs)
      (x:Exp)
      (h: rw_bisim l (eval (kr x)))
      : rw_bisim l (.abs kr)

end Cs

end Functional

namespace Wit_gen

-- a list with continuations
inductive Wg where
  | nil : Wg
  | cons : Exp -> Wg -> Wg
  | input : (Exp -> Wg) -> Wg

def to_wg (c:Circuit) : Wg :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c
  | .assert_bool _ c => to_wg c
  | .lam k => Wg.input (fun i => to_wg (k i))
  | .share e k =>
    let e := eval_e e
    .cons e (to_wg (k e))
  | .inv e k =>
    let inv : Exp := .c e⁻¹ -- TODO need to check for 0?
    .cons inv (to_wg (k inv))
  | .is_zero e k =>
    let inv : Exp := .c e⁻¹ -- TODO need to check for 0?
    let o := .c (if eval_e e = 0 then 1 else 0)
    .cons inv (.cons o (to_wg (k o)))
  | .assert_limb e c =>
    let e := eval_e e
    if e.val < 4
    then
      let es : Vector Exp 2 := (decomp e).map .c
      .cons es[0] (.cons es[1] (to_wg c))
    else
      .nil -- fail

def wrap (c:Cs) (gt:Wg) : Cs :=
  match c with
  | Cs.nil => Cs.nil
  | Cs.eq0 e c => Cs.eq0 e (wrap c gt)
  | Cs.lam k =>
    match gt with
    | Wg.nil => Cs.eq0 1 Cs.nil -- TODO this case can be removed with a index, maybe not worth it
    | Wg.cons x gt => wrap (k x) gt
    | Wg.input k_gt => Cs.lam (fun x => wrap (k x) (k_gt x))

end Wit_gen

namespace To_cs

def to_cs (c:Circuit) : Cs :=
  match c with
  | .nil => Cs.nil
  | .eq0 e c => Cs.eq0 e (to_cs c)
  | .lam k => Cs.lam (fun x => to_cs (k x))
  --
  | .inv e k =>
      Cs.lam (fun inv =>
        Cs.eq0 (1 - (inv * e)) (to_cs (k inv))) -- 1 - inv * e = 0
  | .share e k =>
      Cs.lam (fun o =>
        Cs.eq0 (e - o) (to_cs (k o)))
  | .is_zero e k =>
      Cs.lam (fun inv =>
        Cs.lam (fun o =>
          Cs.eq0 (1 - inv * e - o)    -- 1 - inv * e = o
            (Cs.eq0 (o * e) (to_cs (k o))))) -- o * e = 0
  | .assert_bool e c =>
      Cs.eq0 (e * (1 - e)) (to_cs c)
  | .assert_limb e c =>
      Cs.lam (fun e0 =>
        Cs.eq0 (e0 * (1 - e0)) -- bool
          (Cs.lam (fun e1 =>
             Cs.eq0 (e1 * (1 - e1)) -- bool
                (Cs.eq0 (e0 + 2 * e1 - e) (to_cs c))))) -- e0 + 2 * e1 = e

open Functional

theorem soundness : ∀ (c:Circuit), Cs.rw_bisim (Circuit.eval c) (Cs.eval (to_cs c)) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,Cs.eval,to_cs]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    split
    exact h
    constructor
  | share e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    apply Cs.rw_bisim.async
    simp [Cs.eval]
    split
    apply h
    constructor
  | inv e k h =>
    apply Cs.rw_bisim.async
    simp [Circuit.eval,Cs.eval, eval_e]
    split
    case inv.h.isTrue he0 =>
      simp [he0]
      constructor
    case inv.h.isFalse he0 =>
      split
      case isTrue hsub =>
        apply h
      case isFalse hsub =>
        constructor
  | is_zero e c h =>
    apply Cs.rw_bisim.async
    apply Cs.rw_bisim.async
    simp [Circuit.eval,Cs.eval, eval_e]
    split
    case is_zero.h.h.isTrue he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    case is_zero.h.h.isFalse he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          simp [eval_e] at hmul
          contradiction
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    exact e
  | assert_bool e c h =>
    simp [Circuit.eval,Cs.eval,to_cs,eval_e]
    split
    . split
      . apply h
      . have hneg : ¬ (eval_e e = 0 ∨ eval_e e = 1) := by grind
        contradiction
    . split
      . have hneg : eval_e e = 0 ∨ eval_e e = 1 := by grind
        contradiction
      . constructor
  | assert_limb e c h =>
    apply Cs.rw_bisim.async
    simp [Cs.eval, eval_e]
    split
    case assert_limb.h.isTrue e0_bool =>
      apply Cs.rw_bisim.async
      simp [Cs.eval, eval_e]
      split
      case h.isTrue e1_bool =>
        simp [Circuit.eval]
        split
        case isTrue el4 =>
          split
          case isTrue comp =>
            apply h
          case isFalse comp =>
            constructor
        case isFalse el4 =>
          split
          case isTrue comp =>
            have neg : ZMod.val (eval_e e) < 4 := by
              sorry
            contradiction
          case isFalse comp =>
            constructor
      case h.isFalse e1_bool =>
        constructor
      sorry
    case assert_limb.h.isFalse e0_bool =>
      constructor
    sorry


def completeness : ∀ (c:Circuit),
  Cs.s_bisim (Circuit.eval c) (Cs.eval (Wit_gen.wrap (to_cs c) (Wit_gen.to_wg c))) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,to_cs]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg]
    split
    exact h
    constructor
  | share e c h =>
    simp [eval_e,Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg]
    apply h
  | inv e c h =>
    simp [eval_e,Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg]
    split
    case inv.isTrue he0 =>
      simp [he0]
      constructor
    case inv.isFalse he0 =>
      split
      case isTrue hsub =>
        apply h
      case isFalse hsub =>
        have hsub_neg : 1 - (eval_e e)⁻¹ * eval_e e = 0 := by grind
        contradiction
  | is_zero e c h =>
    simp [eval_e,Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg]
    split
    case is_zero.isTrue he0 =>
      simp
      rw [he0]
      apply h
    case is_zero.isFalse he0 =>
      simp
      split
      case isTrue he0' =>
        apply h
      case isFalse he0' =>
        have he0'_neg : 1 - (eval_e e)⁻¹ * eval_e e = 0 := by grind
        contradiction
  | assert_bool e c h =>
    simp [Circuit.eval,Cs.eval,to_cs,Wit_gen.wrap,Wit_gen.to_wg,eval_e]
    split
    . split
      . apply h
      . have hneg : ¬ (eval_e e = 0 ∨ eval_e e = 1) := by grind
        contradiction
    . split
      . have hneg : eval_e e = 0 ∨ eval_e e = 1 := by grind
        contradiction
      . constructor
  | assert_limb e c h =>
    simp [Circuit.eval,to_cs,Wit_gen.to_wg,decomp]
    split
    case assert_limb.isTrue he0 =>
      simp [eval_e,Cs.eval,Wit_gen.wrap]
      split
      case isTrue comp =>
        split
        case isTrue comp2 =>
          split
          case isTrue comp3 =>
            apply h
          case isFalse comp3 =>
            have hmy : ∀ (n:F), n *2 /2 = n := by grind
            simp [hmy (eval_e e)] at comp comp2 comp3
            have hmy : 2 * (eval_e e / 2) - eval_e e = 0 := by grind
            contradiction
        case isFalse comp2 =>
          have comp2_n : ((eval_e e = 0 ∨ (2:F) = 0) ∨ 1 - eval_e e / 2 = 0) := by sorry
          contradiction
      case isFalse comp =>
        have hmy : ∀ (n:F), n *2 /2 = n := by grind
        simp [hmy (eval_e e)] at comp
    case assert_limb.isFalse he0 =>
      simp [eval_e,Cs.eval,Wit_gen.wrap]
      constructor

end To_cs

namespace Unshare

def unshare (pos:Nat) (c:Circuit) : Circuit :=
  match c with
  | .nil => c
  | .eq0 e c => .eq0 e (unshare pos c)
  | .lam k => .lam (fun x => unshare pos (k x))
  | .inv e k => .inv e (fun x => unshare pos (k x))
  | .is_zero e k => .is_zero e (fun x => unshare pos (k x))
  | .assert_bool e c => .assert_bool e (unshare pos c)
  | .assert_limb e c => .assert_limb e (unshare pos c)
  --
  | .share e k =>
    if pos = 0 then k (eval_e e)
    else .share e (fun x => unshare (pos-1) (k x))

def unshare_all (c:Circuit) : Circuit :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e (unshare_all c)
  | .lam k => .lam (fun x => unshare_all (k x))
  | .inv e k => .inv e (fun x => unshare_all (k x))
  | .is_zero e k => .is_zero e (fun x => unshare_all (k x))
  | .assert_bool e c => .assert_bool e (unshare_all c)
  | .assert_limb e c => .assert_limb e (unshare_all c)
  --
  | .share e k => k (eval_e e)

open Functional.Circuit

theorem unshare_sem_pre : ∀ (c:Circuit), s_bisim (eval c) (eval (unshare_all c)) := by
  intros c
  induction c with
  | lam k h =>
    unfold unshare_all
    constructor
    exact h
  | nil
  | _ _ _ h =>
    unfold unshare_all ; simp [eval] ; first | constructor | apply h | apply same | (split ; repeat (first | apply h | constructor))

end Unshare

namespace Cfold

def cfold_e (e: Exp) : Exp :=
  match e with
  | .c i => .c i
  | l + r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l+r)
    |    l , .c 0 => l
    | .c 0 , r    => r
    |    _ , _    => l + r
  | l * r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l * r)
    |    _ , .c 0
    | .c 0 , _    => .c 0
    |    l , .c 1 => l
--  | .c 1 , r    => r -- TODO
    |    _ , _    => l * r
  | .sub l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l-r)
    |    l , .c 0 => l
    |    _ , _    => .sub l r

def cfold (c:Circuit) : Circuit :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 (cfold_e e) (cfold c)
  | .lam k => .lam (fun x => cfold (k x))
  | .share e k => .share (cfold_e e) (fun x => cfold (k x))
  | .inv e k => .inv (cfold_e e) (fun x => cfold (k x))
  | .is_zero e k => .is_zero (cfold_e e) (fun x => cfold (k x))
  | .assert_bool e c => .assert_bool (cfold_e e) (cfold c)
  | .assert_limb e c => .assert_limb (cfold_e e) (cfold c)

theorem cfold_e_sem_pre : ∀ (e:Exp), (eval_e e) = (eval_e (cfold_e e)) := by
  intros e
  induction e with
  | c f =>
    unfold cfold_e
    simp [eval_e]
  | add l r hl hr =>
    unfold cfold_e
    simp [eval_e]
    split
    repeat simp [*,eval_e]
  | mul l r hl hr =>
    unfold cfold_e
    simp [eval_e]
    split
    repeat simp [*,eval_e]
  | sub l r hl hr =>
    unfold cfold_e
    simp [eval_e]
    split
    repeat simp [*,eval_e]


open Functional.Circuit

theorem cfold_sem_pre : ∀ (c:Circuit), s_bisim (eval c) (eval (cfold c)) := by
  intros c
  induction c with
  | lam k h =>
    unfold cfold
    constructor
    exact h
  | nil => simp [eval]; constructor
  | eq0 e c h =>
    unfold cfold
    simp [eval]
    split
    case eq0.isTrue he =>
      rw [cfold_e_sem_pre] at he
      simp [he]
      apply h
    case eq0.isFalse he =>
      rw [cfold_e_sem_pre] at he
      simp [he]
      constructor
  | share e c h =>
    unfold cfold
    simp [eval]
    rw [<- cfold_e_sem_pre]
    apply h
  | inv e c h =>
    unfold cfold
    simp [eval]
    rw [<- cfold_e_sem_pre]
    split
    . constructor
    . apply h
  | is_zero e c h =>
    unfold cfold
    simp [eval]
    rw [<- cfold_e_sem_pre]
    split
    . apply h
    . apply h
  | assert_bool e c h =>
    unfold cfold
    simp [eval]
    rw [<- cfold_e_sem_pre]
    split
    . apply h
    . constructor
  | assert_limb e c h =>
    unfold cfold
    simp [eval]
    rw [<- cfold_e_sem_pre]
    split
    . apply h
    . constructor

end Cfold


/-
  Relational big-step semantics, could be useful to go from Lean to Circuit. In that case we would need to prove equivalence with the functional one.
-/
namespace Relational
-- no need for option

namespace Circuit
inductive eval : Circuit -> Circuit -> Prop where
  | nil : eval .nil .nil
  | lam
      (k:Exp -> Circuit)
      : eval (.lam k) (.lam k)
  | eq0_t
      (e:Exp)
      (c:Circuit)
      (h:eval_e e = 0)
      : eval (.eq0 e c) c
  | is_zero
      (e:Exp)
      (k:Exp -> Circuit)
      (b:Exp)
      (h:(eval_e e = 0 → b = .c 1) ∧ (eval_e e ≠ 0 -> b = .c 0))
      : eval (.is_zero e k) (k b)

inductive s_bisim : (l r: Circuit) -> Prop where
  | true
      : s_bisim .nil .nil
  | sync
      (kl kr:Exp -> Circuit)
      (lres rres:Circuit)
      (h: ∀ x,
        (hl: eval (kl x) lres) ->
        (hr: eval (kr x) rres) ->
        s_bisim lres rres)
      : s_bisim (.lam kl) (.lam kr)

end Circuit

namespace Cs
inductive eval : Cs -> Cs -> Prop where
  | nil : eval .nil .nil
  | lam
      (k:Exp -> Cs)
      : eval (.lam k) (.lam k)
  | eq0_t
      (e:Exp)
      (cs:Cs)
      (h:eval_e e = 0)
      : eval (.eq0 e cs) cs

inductive s_bisim : (l: Circuit) -> (r: Cs) -> Prop where
  | true
      : s_bisim .nil .nil
  | sync
      (kl:Exp -> Circuit)
      (kr:Exp -> Cs)
      (lres:Circuit)
      (rres:Cs)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Cs.eval (kr x) rres) ->
        s_bisim lres rres)
      : s_bisim (.lam kl) (.lam kr)

inductive rw_bisim : (l: Circuit) -> (r: Cs) -> Prop where
  | true
      : rw_bisim .nil .nil
  | sync
      (kl:Exp -> Circuit)
      (kr:Exp -> Cs)
      (lres:Circuit)
      (rres:Cs)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Cs.eval (kr x) rres) ->
        rw_bisim lres rres)
      : rw_bisim (.lam kl) (.lam kr)
  | async
      (l:Circuit)
      (kr:Exp -> Cs)
      (rres:Cs)
      (x:Exp)
      (h: Cs.eval (kr x) rres -> rw_bisim l rres)
      : rw_bisim l (.lam kr)

end Cs

end Relational

namespace Denotational

inductive Den where
  | bool : Option Unit -> Den
  | input : (F -> Den) -> Den

def eval (c:Circuit) : Den :=
  match c with
  | .nil => Den.bool (some ())
  | .eq0 e c =>
    if eval_e e = 0 then eval c else Den.bool none
  | .lam k => Den.input (fun i => eval (k (.c i)))
  | .share e k => eval (k e)
  | .inv e k => eval (k (.c (if eval_e e = 0 then 0 else 1 / eval_e e)))
  | .is_zero e k =>
    if eval_e e = 0 then eval (k (.c 1)) else eval (k (.c 0))
  | .assert_bool e c =>
    if eval_e e ∈ [0,1] then eval c else Den.bool none
  | .assert_limb e k => sorry

inductive rw_bisim : (l r:Den) -> Prop where
  | bool
      (b:Option Unit)
      : rw_bisim (Den.bool b) (Den.bool b)
  | sync
      (kl:F -> Den)
      (kr:F -> Den)
      (hrec: ∀ x, rw_bisim (kl x) (kr x))
      : rw_bisim (Den.input kl) (Den.input kr)
  | async
      (h:Den)
      (kr:F -> Den)
      (x:F) -- ∃ x
      (hrec: rw_bisim h (kr x))
      : rw_bisim h (Den.input kr)

end Denotational

end Hoas
