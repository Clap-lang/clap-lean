import Clap.Primes
import Clap.Spec
import Clap.BitVec
import Clap.Lang

open Clap.Lang

variable {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)]

structure RawPoint (p : ℕ) where
  x : F p
  y : F p

structure Point (p : ℕ) [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] where
  x : F8 p
  y : F8 p

def RawPoint.validate (a: RawPoint p) : Option (Point p) := do
  let x ← F8.ofF a.x
  let y ← F8.ofF a.y
  some {x, y}

def check (x y: F8 p) : Option Unit := do
  F8.assertEq x y


def PrivateInput (α : Type) := α
def PublicInput (α : Type) := α

/-
- the two check instances can be done independently in parallel
- the same function check can be re-used
-/

def circuit
  (pub_p : PublicInput (Point p))
  (pri_p : PrivateInput (RawPoint p)) : Option Unit := do
  let pri_p ← pri_p.validate
  check pub_p.x pri_p.x
  check pub_p.y pri_p.y

-- -- and recomposed in this new function that is defEq with the original (just need some beta)

-- def keyless' (x y : FString p 3) : Option Unit := do
--   keyless1 x y
--   keyless2 x.len y.len

-- def check1 (x : FString p 3) : Option Unit := do
--   eq0 x.len

-- def check2 (x : FString p 3) : Option Unit := do
--   let l ← share x.len
--   let v ← num2bits 2 l
--   eq0 v.sum
--   eq0 l

/- This is the result of compiler. A program fully reduced to a flat sequence of basic operands. -/
namespace Circuit

def check (x : FString p 3) : Option Unit := do
  let l ← share x.len
  let v ← num2bits 2 l
  eq0 (v[0]! + v[1]!)

end Circuit

/- Heterogeneous lists -/
inductive HList : List Type → Type 1 where
  | nil : HList []
  | cons : {α : Type} → {ts : List Type} → α → HList ts → HList (α :: ts)

def append {α β} (x : HList α) (y : HList β) : HList (α ++ β) :=
  match x with
  | .nil => y
  | .cons x l => .cons x (append l y)

def ex : HList ([Bool, String, Nat]) := .cons true (.cons "" (.cons 1 .nil))

/-
  A Witness Generator is a function that takes the same inputs as the circuit
  (even if some may be unused) and returns a heterogeneous list.
-/
namespace Wg

def check (x : FString p 3) : HList [(ZMod p), List (ZMod p)] :=
  let l := x.len
  HList.cons l (
  let v := Clap.num2bitsLsbPure 2 x.len
  HList.cons v
  HList.nil)

end Wg

/-
  The Constraint System takes the same inputs as the circuit. It returns a
  series of Option values that can either be functions to receive any auxiliary
  input or ().
-/
namespace Cs

def check (x : FString p 3) : Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)) :=
  some (fun (l:ZMod p) ↦ do
  eq0 (x.len - l)
  some (fun (v:Vector (ZMod p) 2) ↦ do
  eq0 (v[0] + (2:ZMod p) * v[1] - l)
  eq0 (v[0] * ((1:ZMod p) - v[0]))
  eq0 (v[1] * ((1:ZMod p) - v[1]))
  eq0 (v[0] + v[1])
  some ()))

end Cs

namespace CsInputsFirst'

def check (x : FString p 3) : Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)) :=
  some (fun (l:ZMod p) ↦
  some (fun (v:Vector (ZMod p) 2) ↦ do
  eq0 (x.len - l)
  eq0 (v[0] + (2:ZMod p) * v[1] - l)
  eq0 (v[0] * ((1:ZMod p) - v[0]))
  eq0 (v[1] * ((1:ZMod p) - v[1]))
  eq0 (v[0] + v[1])
  some ()))

end CsInputsFirst'

namespace CsInputsFirst

def check (x : FString p 3) : ZMod p → Vector (ZMod p) 2 → Option Unit :=
  fun (l:ZMod p) ↦
  fun (v:Vector (ZMod p) 2) ↦ do
  eq0 (x.len - l)
  eq0 (v[0] + (2:ZMod p) * v[1] - l)
  eq0 (v[0] * ((1:ZMod p) - v[0]))
  eq0 (v[1] * ((1:ZMod p) - v[1]))
  eq0 (v[0] + v[1])
  some ()

end CsInputsFirst

namespace CsList

def check (x : FString p 3) : ZMod p → Vector (ZMod p) 2 → List (ZMod p) :=
  fun (l:ZMod p) ↦
  fun (v:Vector (ZMod p) 2) ↦
  [
    x.len - l,
    v[0] + (2:ZMod p) * v[1] - l,
    v[0] * ((1:ZMod p) - v[0]),
    v[1] * ((1:ZMod p) - v[1]),
    v[0] + v[1]
  ]

end CsList

namespace Completeness

inductive wrapExt : {tc tcs: Type} → {twg : Type 1} → tc → twg → tcs → Prop where
  | none {t : Type} : wrapExt none      _         none
  | same {t : Type} : wrapExt (some ()) HList.nil (some ())
  | lam {α tl tr : Type} {twg} {kl : α → tl} {wg : α → twg} {kr : α → tr}
        (h : ∀ x, wrapExt (kl x) (wg x) (kr x)) : wrapExt kl wg kr
  | right {α tl tr : Type} {l : tl} {x:α} {wg} {kr : α → tr}
        (h : wrapExt l wg (kr x)) : wrapExt l (HList.cons x wg) (some kr)

lemma wrapExtShare {tl tr : Type} {twg : List Type}
  (kl : ZMod p → Option tl)
  (kr : ZMod p → Option tr)
  (wg : HList twg)
  (e : ZMod p)
  (h : wrapExt (kl e) wg (kr e)) :
  wrapExt
    (bind (share e) kl)
    (HList.cons e wg)
    (some (fun s ↦ do eq0 (e - s) ; kr s))
:= by
  simp [share,eq0]
  constructor
  simp
  assumption

lemma wrapExtNum2bits [Fact (2 < p)] [Fact (Nat.Prime p)] {tl tr : Type} {twg : List Type}
  (kl : List (ZMod p) → Option tl)
  (kr : List (ZMod p) → Option tr)
  (wg : HList twg)
  (w:ℕ) (e : ZMod p)
  (bits : List (ZMod p))
  (hbits : bits = Clap.num2bitsLsbPure w e)
  (h : wrapExt (kl bits) wg (kr bits)) :
  wrapExt
    (bind (num2bits w e) kl)
    (HList.cons bits wg)
    (some (fun (v:List (ZMod p)) ↦ do
       eq0 (Clap.bits2num v - e)
       List.foldrM (fun b () ↦ eq0 (b * ((1:ZMod p) - b))) () v
       kr v))
:= by
  simp [num2bits]
  split
  case _ ebound =>
    simp
    apply wrapExt.right
    rw [hbits]
    rw [Clap.bits2num_of_num2bitsLsbPure_eq]
    simp [eq0]
    sorry
    sorry
  case _ ebound =>
    simp
    apply wrapExt.right
    sorry

lemma completeness :
  wrapExt
    (Circuit.check : FString p 3 → Option Unit)
    (Wg.check : FString p 3 → HList [(ZMod p), List (ZMod p)])
    (Cs.check : FString p 3 → Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)))
:= by
  unfold Circuit.check Wg.check Cs.check
  constructor ; intro
  apply wrapExtShare
 -- apply wrapExtNum2bits
  sorry

end Completeness

namespace Soundness

inductive wrExt : Π {tl tr: Type}, tl → tr → Prop where
  | same {t : Type} {c : t} : wrExt c c
  | lam {α tl tr : Type} {kl : α → tl} {kr : α → tr}
        (h : ∀ x, wrExt (kl x) (kr x)) : wrExt kl kr
  | none {t : Type} {c : t} : wrExt c none
  | right {α tl tr : Type} {l : tl} {kr : α → tr}
        (h : ∀ x, wrExt l (kr x)) : wrExt l (some kr)

lemma shareWrExt {tl tr : Type}
  (kl : ZMod p → Option tl)
  (kr : ZMod p → Option tr)
  (e : ZMod p)
  (h : ∀ x, wrExt (kl x) (kr x)) :
  wrExt
    (bind (share e) kl)
    (some (fun s ↦ do eq0 (e - s) ; kr s))
:= by
  simp +zeta only [share]
  constructor
  intro s
  by_cases he : e - s = 0
  · have h0 : eq0 (p:=p) 0 = some () := by simp [eq0]
    rw [he]
    rw [sub_eq_zero] at he
    rw [<-he]
    simp [h0]
    apply h
  · have hn0 e : e≠0 → eq0 (p:=p) e = none := by simp [eq0]
    apply hn0 (e-s) at he
    rw [he]
    simp
    constructor

lemma num2bitsWrExt {tl tr : Type} {w:ℕ}
  (kl : List (ZMod p) → Option tl)
  (kr : List (ZMod p) → Option tr)
  (e : ZMod p)
  (h : ∀ x, wrExt (kl x) (kr x)) :
  wrExt
    (bind (num2bits w e) (fun x ↦ kl x))
    (some (fun bits ↦ do
       eq0 (Clap.bits2num bits - e)
       List.foldlM (fun () b ↦ eq0 (b * ((1:ZMod p) - b))) () bits
       kr bits))
:= by sorry

lemma equiv_circuit_cs :
  wrExt
    (Circuit.check : FString p 3 → Option Unit)
    (Cs.check : FString p 3 → Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)))
:= by
  unfold Circuit.check Cs.check
  constructor
  intro x
  apply shareWrExt
  intro l
  -- need vector in num2bits to simp
  -- aesop (add simp [Circuit.check,ToCs.check,num2bits,share,eq0,accept,shareWrSim,num2bitsWrSim]) (add unsafe constructors wrBisimLean)
  sorry

end Soundness

-- tl = F → Option (F → ... → Option Unit)
-- tr = F → F → ... → Option Unit
inductive extAsyncLam : Π {th : List Type} {tl tr: Type}, HList th → tl → tr → Prop where
  | none : extAsyncLam _ none none -- the types can be different and not unit
  | some {l : Option Unit} : extAsyncLam .nil l l
  | lamR {tl tr α : Type} {thl : List Type} {l : HList thl} {kl : tl} {kr : α → tr}
        (h : ∀ x, extAsyncLam (append l (.cons x .nil)) kl (kr x))
        : extAsyncLam l kl kr
  | lamL {tl tr α : Type} {x:α} {l} {kl : α → tl} {kr : tr}
        (h : extAsyncLam l (kl x) kr)
        : extAsyncLam (.cons x l) kl kr
  | lamI {tl tr α : Type} {x:α} {l} {kl : α → tl} {kr : tr}
        (h : extAsyncLam l (kl x) kr)
        : extAsyncLam (.cons x l) (some kl) kr

lemma equiv_cs_csInputsFirst :
  extAsyncLam
    .nil
    (Cs.check : FString p 3 → Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)))
    (CsInputsFirst.check : FString p 3 → ZMod p → Vector (ZMod p) 2 → Option Unit)
:= by
  unfold Cs.check CsInputsFirst.check
  apply extAsyncLam.lamR ; intro x
  apply extAsyncLam.lamL
  apply extAsyncLam.lamR ; intro l
  apply extAsyncLam.lamI
  apply extAsyncLam.lamR ; intro v
  simp [eq0,append]
  split
  . simp
    apply extAsyncLam.lamI
    constructor
  . simp
    constructor
--  repeat (first | constructor | intro )
--  aesop (add simp [cs,cs']) (add unsafe constructors extAsyncLam)


-- tl = F → F → ... → Option Unit
-- tr = F → F → ... → List F
inductive extList : Π {tl tr: Type}, tl → tr → Prop where
  | nil : extList (some ()) []
  | cons {e : ZMod p} {kl : Option Unit} {kr : List (ZMod p)}
        (h : extList kl kr) : extList (bind (eq0 e) (fun () ↦ kl)) (e::kr)
  | lam {α tl tr : Type} {kl : α → tl} {kr : α → tr}
        (h : ∀ x, extList (kl x) (kr x)) : extList kl kr

lemma equiv_csInputsFirst_csList :
  extList (p:=p)
    (CsInputsFirst.check : FString p 3 → ZMod p → Vector (ZMod p) 2 → Option Unit)
    (CsList.check : FString p 3 → ZMod p → Vector (ZMod p) 2 → List (ZMod p))
:= by
  unfold CsInputsFirst.check CsList.check
  repeat (first | constructor | intro)

inductive sBisimList' : Π {tl tr: Type}, tl → tr → Prop where
  | list {kl : Option Unit} {kr : List (ZMod p)}
        (h : List.all kr (· = 0) → kl = some ()) : sBisimList' kl kr
  | lam {tl tr : Type} {kl : ZMod p → tl} {kr : ZMod p → tr}
        (h : ∀ x, sBisimList' (kl x) (kr x)) : sBisimList' kl kr

lemma equiv'_csInputsFirst_csList :
  sBisimList' (p:=p)
    (CsInputsFirst.check : FString p 3 → ZMod p → Vector (ZMod p) 2 → Option Unit)
    (CsList.check : FString p 3 → ZMod p → Vector (ZMod p) 2 → List (ZMod p))
 := by
  unfold CsInputsFirst.check CsList.check
--  aesop (add simp [eq0,accept]) (add safe constructors sBisimList')
  sorry
-- lemma sound_InputsFirst_cs (e s : ZMod p) :
--   csInputsFirst e s = some () → (bind (cs e) (fun f ↦ f s)) = some ()
-- := by
--   aesop (add simp [csInputsFirst,cs,eq0,accept])

-- lemma sound_csList_csInputsFirst (e s : ZMod p) :
--   (List.all (csList e s) fun e ↦ e = 0) → csInputsFirst e s = some ()
-- := by
--   aesop (add simp [csList,csInputsFirst,eq0,accept])

namespace Optimizations

def ex_circuit (v : Vector (ZMod Primes.bn254) 2)
               (expected : ZMod Primes.bn254) : Option Unit := do
  let prod0 ← share v[0]
  let prod  ← share (v[1] * prod0)
  eq0 (prod - expected)
  eq0 (prod - expected)

def ex_circuit_inlined (v : Vector (ZMod Primes.bn254) 2)
                   (expected : ZMod Primes.bn254) : Option Unit := do
  eq0 (v[1] * v[0] - expected)
  eq0 (v[1] * v[0] - expected)

lemma equiv : ex_circuit_inlined = ex_circuit := by
  unfold ex_circuit ex_circuit_inlined
  simp [share]

def ex_circuit_dedup (v : Vector (ZMod Primes.bn254) 2)
                     (expected : ZMod Primes.bn254) : Option Unit := do
  eq0 (v[1] * v[0] - expected)

lemma equiv' : ex_circuit_dedup = ex_circuit := by
  unfold ex_circuit ex_circuit_dedup
  aesop (add simp [share,eq0])

end Optimizations



namespace Simulations

/-
LTS for a pure functional language
- states: any reduced term, so either λx.y or a ground term such as () and a special state stop
- labels: any input and the final state
- transitions: any application or final state

R is a simulation:
∀ p q, R p q →
if p -a-> p' then q -a-> q' ∧ R p' q'
-/


inductive FunExt : Π {l r: Type}, l → r → Prop where
  | same {t : Type} {x : t} : FunExt x x
  | lam {α tl tr : Type} {kl : α → tl} {kr : α → tr}
        (h : ∀ x, FunExt (kl x) (kr x)) : FunExt kl kr

example : FunExt (fun (x:ℕ) ↦ x) (fun (x:ℕ) ↦ 0+x) := by
  apply FunExt.lam ; intro ; simp ; apply FunExt.same
--  apply funExt.same works for x+0

example : (fun (x:ℕ) ↦ x) = (fun (x:ℕ) ↦ 0+x) := by
  funext
  rw [zero_add]

inductive Simulates : {l r: Type} → l → r → Prop where
  | sim : {α tl tr : Type} →
          ∀ (x:α) (p : α → tl) (q : α → tr), Simulates q p →
          Simulates (q x) (p x) → Simulates q p

end Simulations
