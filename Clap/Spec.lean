import Mathlib.Data.ZMod.Basic

import Clap.Circuit
import Clap.Simulation

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]

namespace Spec

@[irreducible]
def eq0 (e : ZMod p) : Option Unit :=
  if e = 0 then some () else none

@[irreducible]
def share (e : ZMod p) : Option (ZMod p) := e

@[irreducible]
def is_zero (e : ZMod p) : Option (ZMod p) := if e = 0 then .some 1 else .some 0

def assert_range (w : ℕ) (e : ZMod p) : Option Unit := if e.val < 2^w then some () else none

-- def assert_range' (w:ℕ) (e:ZMod p) : Option ({f:ZMod p | f.val < 2^w}) := if h:e.val < 2^w then some ⟨e,h⟩ else none

def div_rem (e:ZMod p) : ZMod p × ZMod p :=
  let d : ℕ := e.val / 256
  let r : ℕ := e.val % 256
  (d,r)

#guard (2:ℕ) / 256 = 0
#guard (2:ZMod prime_babybear) / 256 ≠ 0
#guard (2:ZMod prime_babybear).val / 256 = 0
#guard Spec.div_rem (p:=prime_babybear) 2 = (0,2)
#guard Spec.div_rem (p:=prime_babybear) 255 = (0,255)
#guard Spec.div_rem (p:=prime_babybear) 256 = (1,0)
#guard Spec.div_rem (p:=prime_babybear) 257 = (1,1)

@[irreducible]
def accept : Unit -> Unit := fun () => ()

/- ----------------------/

def succ (i : UInt8) : UInt8 := i + 1

abbrev FU8 (p:ℕ) : Type := {f : ZMod p | f.val < 2^8}

def coe_fu8_uint8 (f:FU8 p) : UInt8 :=
  if p > 256 then UInt8.ofNat f.val.val else 0

-- TODO Coe? CoeOut?
-- instance coeout_fu8 [Fact (256 < p)] : CoeOut (FU8 p) UInt8 where
--   coe f := UInt8.ofNat f.val.val

instance coe : CoeOut (FU8 p) UInt8 where
  coe := coe_fu8_uint8

-- we should be able to write this
-- instance [Fact (256 < p)] : CoeOut UInt8 (FU8 p) where
--   coe f := ⟨f.toNat, by
--   have h := f.toNat_lt_size
--   simp [UInt8.size] at h
--   simp
--   apply lt_trans (c:=p) at h
--   rw [Ordinal.mod_eq_of_lt]
--    ⟩

namespace FU8

-- we can't write this
-- instance [Fact (2*256 < p)] : HAdd (FU8 p) (FU8 p) (FU8 p) where
--   hAdd a b := ⟨a.val + b.val, by simp ;  ⟩

def add (a b : ZMod p) : Option (ZMod p) := do
  let o := a + b
  assert_range 8 o
  o

def add' (a b :FU8 p) : Option (FU8 p) :=
  let o := a.val + b.val
  assert_range' 8 o

end FU8

-- theorem refine_add_mixed [Fact (256<p)] : ∀ (a b:FU8 p),
--   assert_range 8 (a.val+b.val) = some () -> UInt8.add a b = a+b := by
--   intros a b
--   simp [assert_range]
--   intro hadd
--   rfl

-- lemma f_add_no_overflow (a b : F p):
--   a.val + b.val < p -> (a + b).val = a.val + b.val
-- := sorry

omit [Fact (Nat.Prime p)] in
lemma f_add_no_overflow_generic (a b : ZMod p) :
  a.val < p / 2 ∧ b.val < p / 2 -> (a + b).val = a.val + b.val
:= by
  rintro ⟨h₁, h₂⟩
  apply ZMod.val_add_of_lt
  apply lt_of_lt_of_le
  swap
  · exact Nat.mul_div_le p 2
  · rw [Nat.two_mul]
    exact Nat.add_lt_add h₁ h₂


--TODO maybe this should start with nat and apply convertions?omit [Fact (Nat.Prime p)] in
omit [Fact (Nat.Prime p)] in
lemma fu8_add_no_overflow (a b : FU8 p):
    256 < p → a.val.val + b.val.val < 256 -> (a.val + b.val).val = a.val.val + b.val.val := by
  intros h' h
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp only at h ⊢
  apply ZMod.val_add_of_lt
  apply lt_trans h h'


-- lemma uint8_ofNat_add (a b : ℕ) :
--   -- a + b < 256 ->
--   UInt8.ofNat (a + b) = UInt8.ofNat a + UInt8.ofNat b
-- := by
--   exact UInt8.ofNat_add a b

-- rw! from Mathlib, adds the right coertion

theorem refine_add' (hp : 256 * 2 < p) (a b o : FU8 p) :
  FU8.add' a b = some o -> UInt8.add a b = o := by
  unfold FU8.add' coe_fu8_uint8
  split_ifs with cond
  · intros h
    have ha := a.2
    have hb := b.2
    rw [Set.mem_setOf_eq] at ha hb
    simp only [Set.coe_setOf, Nat.reducePow, assert_range', Set.mem_setOf_eq,
      Option.dite_none_right_eq_some, Option.some.injEq] at h
    rcases h with ⟨h', h⟩
    rw [←h]
    have : a.val.val + b.val.val < p := by
      refine lt_trans ?_ hp
      rw [Nat.mul_two]
      exact Nat.add_lt_add ha hb
    rw [@ZMod.val_add, Nat.mod_eq_of_lt this]
    aesop
  · intros h; rfl


def succ_c' (i:FU8 p) : Option (FU8 p) := do
  let o : ZMod p := i.val + 1
  assert_range' 8 o

def succ_c (i:ZMod p) : Option (ZMod p) := do
  let o : ZMod p := i.val + 1
  assert_range 8 o
  o

theorem refine [Fact (256 < p)] : ∀ (i_c o_c : ZMod p) (i o : UInt8),
    UInt8.ofNat i_c.val = i →
    UInt8.ofNat o_c.val = o →
    succ_c i_c = some o_c →
    succ (UInt8.ofNat i_c.val) = o := by
  intros i_c o_c i o hi ho
  simp only [succ_c, assert_range, ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.reducePow,
    Option.bind_eq_bind, succ]
  split_ifs with h
  · intros h'
    simp only [Option.bind_some, Option.some.injEq] at h'
    have : i_c.val < 256 := by
      rw [ZMod.val_add, ZMod.val_one] at h
      rcases Nat.eq_or_lt_of_le (ZMod.val_lt i_c) with h'' | h''
      ·

        sorry
      · rw [Nat.mod_eq_of_lt h''] at h
        linarith
    rw [h'] at h
    rw [hi]



    sorry
  · intros h
    simp at h
  -- -- case _ h =>
  -- -- have hu8: i_c.val < 256 := sorry
  -- -- simp
  -- -- intro ho_c
  -- -- rw [ZMod.val_add_of_lt] at h
  -- -- rw [←hi,←ho,←ho_c]
  -- -- simp [UInt8.ofNat]
  -- -- apply ZMod.val_natCast_of_lt (n:=p) at h
  -- -- rw [<-h]
  -- sorry

-- theorem refine' [Fact (256<p)] : ∀ (i_c o_c:FU8 p) (i o:UInt8),
--   succ_c' i = some o -> succ i_c = o_c := by
--   intros i_c o_c i o
--   simp [succ_c',succ]
--   simp [assert_range']
--   intro h bla
--   rw [<-bla]
--   simp
--   have h256 : 256<p := sorry
--   apply lt_trans (c:=p) at h
--   apply h at h256


--   rw [ZMod.val_add_of_lt]
--   rw [ZMod.val_one]
--   simp
--   rw [ZMod.val_one]

--   rw [ZMod.val_add_of_lt] at h
--   rw [ZMod.val_one] at h
--   sorry -- assumption
--   assumption
--   simp
--   let hi_c := i_c.prop
--   rw [<-ZMod.val_add_of_lt]
--   apply lt_trans
--   apply h
--   rw [<-ZMod.val_add_of_lt]
--   apply lt_trans
--   apply h

--   apply ZMod.val_natCast_of_lt (n:=p) at h
--   sorry

lemma bla [Fact (256<p)] : ∀ (a:FU8 p), (a:UInt8).toNat = a.val := sorry

set_option pp.parens true

-- theorem refine_add [Fact (256<p)] : ∀ (a b o:ZMod p),-- (i:UInt8),
--   assert_range 8 (a+b) = some () -> UInt8.add a b = o := by
--   intros a b o
--   simp [assert_range']
--   intro hadd ho
--   rw [<-ho]
--   rw [ZMod.val_add_of_lt]
--   simp
--   rfl

-- theorem refine_add'' [Fact (2*256<p)] [Fact (256<p)] : ∀ (a b o:FU8 p),
--   assert_range' 8 (a.val+b.val) = some o -> UInt8.add a b = o := by
--   intros a b o
--   simp [assert_range']
--   intro hadd ho
--   rw [<-ho]
--   rw [ZMod.val_add_of_lt]
--   simp
--   rfl

--   let ho' := o.prop
--   rw [<-ho] at ho'
--   simp at ho' -- same Hadd

--   have ha : _ := bla a
--   have hb : _ := bla b
--   simp at ha hb
--   rw [<-ha]
--   rw [<-hb]
--   simp
--   rfl

--   simp
--   have h: 256<p := sorry

--   simp [Function.InjeAlso, any thoughts on yoctive] at ha
--   injection ha
--   rw [<-ha]
--   rw [<-hb]
-- --  rw [ZMod.val_intCast]
--   aesop
--  have h256 : 256<p := sorry
--   apply lt_trans (c:=p) at h
--   apply h at h256


/- -----------/

/-
  Expand a function that takes a vector of n Felts, into a series of n
  functions taking a single Felt.
  e.g. Vector F 2 -> Option Unit  ~>  F -> F -> Option Unit
-/
@[reducible]
def typ (a r : Type) : ℕ -> Type
  | 0   => r
  | n+1 => a -> typ a r n

@[reducible]
def curry {a r : Type} (n : ℕ) (k : Vector a n -> r) : typ a r n :=
  match n with
  | 0 => k ⟨#[], by rfl⟩
  | n+1 => fun (x : a) => curry n (fun l => k (Vector.push l x))

#guard curry 2 (fun x => x[0] == 0 && x[1] == 1) 1 0 = True

lemma equiv_eq0 (el : ZMod p) (er : Expₑ p) (cl : Option Unit) (cr : Circuitₑ p) :
    el = Exp.eval er ->
    Simulation.s_bisim cl (Circuit.eval cr) ->
    Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  intro he hc
  simp only [Circuit.eval,Option.bind,eq0]
  split
  split
  case _ _ heq her =>
    rw [her] at he
    rw [he] at heq
    simp at heq
  case _ _ hel her =>
    constructor
  case _ _ _ hel =>
    simp at hel
    rw [he] at hel
    simp
    split
    . apply hc
    . contradiction

lemma equiv_share (el : ZMod p) (er : Expₑ p) (kl : ZMod p -> Option Unit) (kr : ZMod p -> Circuitₑ p) :
  el = Exp.eval er ->
  (∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) ->
  Simulation.s_bisim (bind (share el) kl) (Circuit.eval (.share er kr)) := by
  intro he hk
  simp only [Circuit.eval,bind,share]
  rw [he]
  apply hk

lemma equiv_assert_range (el : ZMod p) (er : Expₑ p) (cl : Option Unit) (cr : Circuitₑ p) (w : ℕ)
  (he : el = Exp.eval er)
  (hc : Simulation.s_bisim cl (Circuit.eval cr)) :
  Simulation.s_bisim (Option.bind (assert_range w el) (fun () => cl)) (Circuit.eval (.assert_range w er cr)) := by
  simp only [Circuit.eval,Option.bind,assert_range]
  split
  split
  case _ _ heq her =>
    simp at heq
    rw [he] at heq
    grind
  case _ _ hel her =>
    constructor
  case _ _ _ hel =>
    simp at hel
    rw [he] at hel
    simp
    split
    . apply hc
    . contradiction

lemma equiv_div_rem (el : ZMod p) (er : Expₑ p) (kl : ZMod p × ZMod p -> Option Unit) (kr : ZMod p × ZMod p -> Circuitₑ p)
  (he : el = Exp.eval er)
  (hc : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (Option.bind (div_rem el) kl) (Circuit.eval (.div_rem er kr)) := by
  simp only [Circuit.eval,Option.bind,div_rem]
  simp [he]
  norm_num
  apply hc

end Spec

namespace Example_base

open Spec

/-
  A circuit is a function from any number of arguments of type F or Vector F to Option Unit.
-/

def ex p (i: ZMod p) : Option Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  assert_range 2 vi
  accept ()

#guard ex 7 0 = some ()
#guard ex 7 1 = none

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .assert_range 2 (.v vi) (
  .nil)))))

theorem equiv :
  Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  constructor
  intro
  apply equiv_eq0
  simp [Exp.eval]
  apply equiv_share
  . simp [Exp.eval]
  . intro
    apply equiv_eq0
    simp [Exp.eval]
    apply equiv_assert_range
    constructor
    constructor

theorem extract :
  ∃ c : Circuit p (ZMod p), Simulation.s_bisim (ex p) (Circuit.eval c) := by
  unfold ex
  simp only [bind]
  refine ⟨?c,?p⟩
  case p =>
--  apply Simulation.s_bisim.lam (F:=(ZMod p)) (fun x => ?kl) (fun x => (Circuit.eval ?kr))
    sorry
  sorry

end Example_base

namespace Example_vec

open Spec

def ex p (is : Vector (ZMod p) 2) : Option Unit := do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  accept ()

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  Circuit.curry 2 (fun is =>
  .eq0 (.v is[0]) (
  .share (.v is[0]) (fun vi =>
  .eq0 (.v vi + .v is[1]) (
  .nil))))

theorem equiv :
  Simulation.s_bisim (curry 2 (ex p)) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  simp only [curry]
  simp only [Circuit.curry]
  repeat (constructor ; intro)
  apply equiv_eq0
  simp [Vector.append, Exp.eval]
  apply equiv_share
  . simp [Vector.append, Exp.eval]
  . intro
    apply equiv_eq0
    simp [Vector.append, Exp.eval]
    constructor

end Example_vec

namespace Example_fold

open Spec

/- TODO these curry should disappear, the signature should be:
def ex p (xs ys zs: Vector (ZMod p) 2) : Option Unit :=
-/
def ex p :=
  curry 2 (fun (xs: Vector (ZMod p) 2) =>
  curry 2 (fun (ys: Vector (ZMod p) 2) =>
  curry 2 (fun (zs: Vector (ZMod p) 2) => do
  let xys := Vector.map (fun ((x,y): ZMod p × ZMod p) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept ()
  )))

#print axioms ex

#guard ex 7 2 4 1 1 3 5 = some 90 -- [2,4] + [1,1] = [3,5]
#guard ex 7 2 4 1 1 3 6 = none

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  Circuit.curry 2 (fun xs =>
  Circuit.curry 2 (fun ys =>
  Circuit.curry 2 (fun zs =>
  .eq0 ((.v xs[0]) + (.v ys[0]) - (.v zs[0])) (
  .eq0 ((.v xs[1]) + (.v ys[1]) - (.v zs[1])) (
  .nil)))))

theorem equiv :
    Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [curry]
  simp only [Circuit.curry]
  repeat (constructor ; intro)
  dsimp
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  simp [Vector.append, Exp.eval]
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  . simp [Vector.append, Exp.eval]
  . simp!
    constructor

end Example_fold

end Clap
