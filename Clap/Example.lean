import Clap.Primes
import Clap.Spec
import Clap.BitVec
import Clap.Lang
import Clap.HashToField

open Clap.Lang

abbrev p := Primes.bn254

structure Data where
  vec : Vector (F p) 2
  n : F8 p

def check (a: Data) : Option Unit := do
  let allZeros ← a.vec.foldlM (fun (acc x:F p) ↦ do acc &&& (←isZero x)) FB.true
  FB.assert allZeros

def Data.validate (d : Data) : Option Unit :=
  F8.validate d.n

def PrivateInput (α : Type) := α
def PublicInput (α : Type) := α

/-
- the two check instances can be done independently in parallel
- the same function check can be re-used
-/

def circuit
  (pub_p : PublicInput Data)
  (pri_p : PrivateInput Data) : Option Unit := do
  pri_p.validate
  check pub_p
  check pri_p
  F.assert_eq pub_p.n pri_p.n

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
namespace Reduced

-- TODO trivial for Unit return type
def check (a: Data) : Option Unit := do
  let a0 ← isZero a.vec[0]
  let a1 ← isZero a.vec[1]
  eq0 (1 - a0 * a1)

def circuit
  (pub_p : PublicInput Data)
  (pri_p : PrivateInput Data) : Option Unit := do
  let _ ← num2bits 8 pri_p.n
  check pub_p
  check pri_p
  eq0 (pub_p.n - pri_p.n)

end Reduced

/-
  A Witness Generator is a function that takes the same inputs as the circuit
  (even if some may be unused) and returns a heterogeneous list.
-/
namespace Wg

-- manual
def isZero (e: F p) : List (F p) :=
  let a := e⁻¹
  let o := if e = 0 then 1 else 0
  a :: o :: []

-- manual
def num2bits (w:ℕ) (e : F p) : Vector (F p) w :=
  Clap.num2bitsLsbPureV w e

-- compiled
def check (a: Data) : List (F p) :=
  isZero a.vec[0] ++ isZero a.vec[1]

-- compiled
def circuit
  (pub_p : PublicInput Data)
  (pri_p : PrivateInput Data) : List (F p) :=
  (num2bits 8 pri_p.n).toList
  ++
  check pub_p
  ++
  check pri_p

end Wg

/-
  The Constraint System takes the same inputs as the circuit. It returns a
  series of Option values that can either be functions to receive any auxiliary
  input or ().
-/
namespace Cs

-- manual
def num2bits (w:ℕ) (e:F p) : Vector (F p) w → Option Unit :=
  fun bits ↦ do
  eq0 (bits2numV bits - e)
  bits.foldrM (fun b () ↦ eq0 (b * ((1:F p) - b))) ()

-- manual
def isZero (e : F p) : (inv o : (F p)) → Option Unit :=
  fun inv o ↦ do
  eq0 (1 - inv * e - o)
  eq0 (o * e)
-- def isZero (e : F p) : (inv o : List (F p)) → Option Unit :=
--   fun inv o ↦ do
--   let inv := inv[0]!
--   let o := o[0]!
--   eq0 (1 - inv * e - o)
--   eq0 (o * e)

-- compiled
def check (a: Data) : (inv0 o0 inv1 o1 : F p) → Option Unit :=
  fun inv0 a0 inv1 a1 ↦ do
  isZero a.vec[0] inv0 a0
  isZero a.vec[1] inv1 a1
  eq0 (1 - a0 * a1)

-- -- compiled
-- def circuit
--   (pub_p : PublicInput Data)
--   (pri_p : PrivateInput Data) : (v : Vector (F p) 8) → (pub_p_inv0 pub_p_a0 pub_p_inv1 pri_p_a1 pri_p_inv0 pri_p_a0 pri_p_inv1 pri_p_a1 : F p) → Option Unit :=
--   fun (v : Vector (F p) 8) (pub_p_inv0 pub_p_a0 pub_p_inv1 pub_p_a1 pri_p_inv0 pri_p_a0 pri_p_inv1 pri_p_a1 : F p) ↦ do
--   num2bits 8 pri_p.n v
--   check pub_p pub_p_inv0 pub_p_a0 pub_p_inv1 pub_p_a1
--   check pri_p pri_p_inv0 pri_p_a0 pri_p_inv1 pri_p_a1
--   eq0 (pub_p.n - pri_p.n)

-- def isZero (e : F p) : (aux : Vector (F p) 1) → (out : Vector (F p) 1) → Option Unit :=
--   fun aux out ↦ do
--   eq0 ((1:F p) - aux[0] * e - out[0])
--   eq0 (out[0] * e)

-- def check (a: Data) : (aux0 aux1 : Vector (F p) 2) → Option Unit :=
--   fun aux0 aux1 ↦ do
--   isZero a.vec[0] aux0
--   isZero a.vec[1] aux1
--   eq0 ((1:F p) - aux0[1] * aux1[1])


end Cs

namespace Soundness

inductive wrExt : Π {tl tr: Type}, tl → tr → Prop where
  | same {t : Type} {c : t} : wrExt c c
  | lam {α tl tr : Type} {kl : α → tl} {kr : α → tr}
        (h : ∀ x, wrExt (kl x) (kr x)) : wrExt kl kr
  | none {t : Type} {c : t} : wrExt c none
  | right {α tl tr : Type} {l : tl} {kr : α → tr}
        (h : ∀ x, wrExt l (kr x)) : wrExt l kr

lemma isZeroWrExt {tl tr : Type}
  (kl : ZMod p → Option tl)
  (kr : ZMod p → Option tr)
  (e inv o : ZMod p)
  (h : ∀ x, wrExt (kl x) (kr x)) :
  wrExt
    (do let o ← isZero e  ; kl o)
    (do Cs.isZero e inv o ; kr o)
:= by
  aesop (add simp [isZero, Cs.isZero,eq0,sub_eq_zero,wrExt.none])

lemma equiv_reduced_cs :
  wrExt Reduced.check Cs.check
:= by
  unfold Reduced.check Cs.check
  apply wrExt.lam ; intro
  apply wrExt.right ; intro
  apply wrExt.right ; intro
  apply wrExt.right ; intro
  apply wrExt.right ; intro
  apply isZeroWrExt ; intro
  apply isZeroWrExt ; intro
  apply wrExt.same

lemma shareWrExt {tl tr : Type}
  (kl : F p → Option tl)
  (kr : F p → Option tr)
  (e s : F p)
  (h : ∀ x, wrExt (kl x) (kr x)) :
  wrExt
    (do let e ← share e ; kl e)
    (do do eq0 (e - s) ; kr s)
:= by
  aesop (add simp [share,eq0,sub_eq_zero])
  constructor

lemma num2bitsWrExt {tl tr : Type} {w:ℕ}
  (kl : Vector (F p) w → Option tl)
  (kr : Vector (F p) w → Option tr)
  (e : F p)
  (bits : Vector (F p) w)
  (h : ∀ x, wrExt (kl x) (kr x)) :
  wrExt
    (do let bs ← num2bits w e ; kl bs)
    (do Cs.num2bits w e bits ; kr bits)
  := by
  unfold num2bits Cs.num2bits eq0
  have h : (bits2numV bits).val < 2^w → (Vector.foldrM (fun b x => if b = 0 ∨ 1 - b = 0 then some () else none) () bits) = some () := sorry
  have h : ¬ (bits2numV bits).val < 2^w → (Vector.foldrM (fun b x => if b = 0 ∨ 1 - b = 0 then some () else none) () bits) = none := sorry
  have h : Clap.num2bitsLsbPureV w (bits2numV bits) = bits := sorry
  aesop (add simp [sub_eq_zero])
  repeat constructor


-- lemma equiv_circuit_cs :
--   wrExt
--     (Circuit.check : FString p 3 → Option Unit)
--     (Cs.check : FString p 3 → Option (ZMod p → Option (Vector (ZMod p) 2 → Option Unit)))
-- := by
--   unfold Circuit.check Cs.check
--   constructor
--   intro x
--   apply shareWrExt
--   intro l
--   -- need vector in num2bits to simp
--   -- aesop (add simp [Circuit.check,ToCs.check,num2bits,share,eq0,accept,shareWrSim,num2bitsWrSim]) (add unsafe constructors wrBisimLean)
--   sorry

end Soundness

namespace Completeness

inductive wrapExt : {tc tcs: Type} → {twg : Type} → tc → twg → tcs → Prop where
  | same {kl kr : Option Unit} (h : kl = kr) : wrapExt kl [] kr
  | lam {α tl tr : Type} {twg} {kl : α → tl} {wg : α → twg} {kr : α → tr}
        (h : ∀ x, wrapExt (kl x) (wg x) (kr x)) : wrapExt kl wg kr
  | right {tkr : Type} {l : Option Unit} {x : F p} {wg : List (F p)} {kr : F p → tkr}
        (h : wrapExt l wg (kr x)) : wrapExt l (x :: wg) kr

lemma wrapExtIsZero
  (kl : F p → Option Unit)
  (kr : Option Unit)
  (e : F p)
  (h : kl (if e = 0 then 1 else 0) = kr) :
    (do let o ← isZero e ; kl o) = (do Cs.isZero e (Wg.isZero e)[0]! (Wg.isZero e)[1]! ; kr)
:= by
  aesop (add simp [isZero,Cs.isZero,Wg.isZero,eq0])

lemma completeness :
  wrapExt
    Reduced.check
    Wg.check
    Cs.check
:= by
  unfold Reduced.check Wg.check Cs.check
  apply wrapExt.lam ; intro x
  apply wrapExt.right
  apply wrapExt.right
  apply wrapExt.right
  apply wrapExt.right
  apply wrapExt.same
  apply wrapExtIsZero
  apply wrapExtIsZero
  rfl

lemma wrapExtShare
  (kl : F p → Option Unit)
  (kr : F p → Option Unit)
  (e : F p)
  (h : kl = kr) :
    (do let e ← share e ; kl e) = (do eq0 (e - e) ; kr e)
:= by
  aesop (add simp [share,eq0,sub_eq_zero])

lemma wrapExtNum2bits [Fact (2 < p)] [Fact (Nat.Prime p)]
  (w:ℕ)
  (kl : Vector (F p) w → Option Unit)
  (kr : Vector (F p) w → Option Unit)
  (e : F p)
  (h : kl = kr) :
    (do let bs ← num2bits w e ; kl bs) =
    (do Cs.num2bits w e (Wg.num2bits w e); kr (Wg.num2bits w e))
  := by
  have h : Vector.foldrM (fun b x => if b = 0 ∨ 1 = b then some () else none) () (Clap.num2bitsLsbPureV w e) = some () := sorry
  have h : ZMod.val e < 2 ^ w → bits2numV (Clap.num2bitsLsbPureV w e) = e := sorry
  have h : ¬ ZMod.val e < 2 ^ w → ¬ bits2numV (Clap.num2bitsLsbPureV w e) = e := sorry
  aesop (add simp [sub_eq_zero,num2bits,Cs.num2bits,Wg.num2bits,eq0])

end Completeness

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
