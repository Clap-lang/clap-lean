/-
this kind of functions are allowed in Phoas, and we need them for:
- optimizations that need to introduce variables
  (which ones exactly? maybe Common Subexp Elim)
- lower to Cs to introduce additional inputs
However we probably don't need them in the source and we can restrict our
compilation to only the `ok` case.
-/

--///////////////////

import Clap.Circuit

--------- Expressions ------------

def equiv_e (t:Exp') (s:Felt) := eval_e' t = s

notation : 65 t:65 "≡" s:66 => equiv_e t s

def eval_c (n:Felt) : (fun _ => Exp.c n) ≡ n := by
  simp [equiv_e, eval_e', eval_e]

def eval_op (el er:Exp') (l r:Felt) :
  el ≡ l → er ≡ r →
  (fun var => Exp.op (el var) (er var)) ≡ (l + r) := by
  intros hl hr;
  simp [equiv_e, eval_e'] at hl hr
  simp [equiv_e, eval_e', eval_e, *]

def a : ∃ e:Exp', e ≡ (1+2) := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )

-- This is only partially true, because we can always reduce an expression
-- (w/o variables) into an Felt, but we won't be producing the AST that we really want.
def parse_e (s:Felt) : ∃ e:Exp', e ≡ s := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )

def plonk (ql qr qo qm qc: Felt) (l r o:Felt) :=
  parse_e (ql * l + qr * r + qo * o + qm * l * r + qc)

-- we do not support abstracting over expressions
example : Felt -> Felt := fun x => x

------------------------------------------

/-
maybe we can define bool (and the other types) as a subtype of felt, so that we can easily cast when they are returned
-/

/- Given that we have the whole program, we can start bottom up and avoid the CPS problem which was spanning from the fact that we needed to build top-down w/o knowing the continuation yet.
-/

/-
If we don't want to pollute the spec with continuations, we need to avoid the
CS style where outputs are replaced by intermediate inputs.
Any function that needs this style, goes in the Phoas costructors.
We will introduce these continuations when lowering Phoas to Cs.

 input_bool : Felt -> Bool :=
   (fun f => assert_bool f; f)

Are we saying that we are writing only ciruits with arrows at the beginning? Can/should we remove cont from Wg?
What happens when we allow it in Cs?
-/


--//// source semantics /////////

-- we can restrict source term to be of type: Felt -> Felt -> ... -> Option Unit
-- first we take all the inputs, then we check them.

def ok : Felt -> Felt -> Option Unit :=
  fun x => fun y => if x=0 then none else if x=y then some () else none

-- this is not ok because we take an input, check it, then take another input
def not_ok : Felt -> Option (Felt -> Option Unit) :=
  fun x => if x = 0 then none else some (fun y => if x=y then some () else none)


-- example source
def eq0 (x:Felt) : Option Unit :=
  if (x = 0) then some () else none

-- example target
def eq0_wg : Wg' := fun var => Wg.lam (fun (x:var) => Wg.eq0 (Exp.v x) Wg.nil)

def nil_s (_:Felt) : Option Unit := some ()
def nil_wg : Wg' := fun var => Wg.lam (fun _:var => Wg.nil)

--/////////////////


inductive Equiv : {a:Type _} -> a -> Wg Felt -> Prop where
  | k :
    {b:Type _} ->
    (s:Felt -> b) ->
    (wg:Wg Felt) ->
    (k:Felt -> Wg Felt) ->
    (eval_wg_rel wg (Wg.lam k) -> ∀ x, Equiv (s x) (k x)) ->
    Equiv s (Wg.lam k)
  | unit :
    (wg:Wg Felt) ->
    (eval_wg_rel wg Wg.nil) ->
    Equiv (some ()) wg

notation : 65 s:65 "≡" t:66 => Equiv s (t Felt)

example : ∃ wg':Wg', some () ≡ wg' := by
  refine ⟨?wg', ?heq⟩
  rotate_left
  constructor
  have h1 : ?wg' Felt = Wg.nil := by rfl
  constructor

example : ∃ wg':Wg', some () ≡ wg' := by
  refine ⟨fun var => ?wg', ?heq⟩
  rotate_left
  constructor

example : ∃ wg':Wg', nil_s ≡ wg' := by
  refine ⟨?wg', ?heq⟩
  rotate_left
--  have h1 : ?wg' = Wg.lam
  apply Equiv.k nil_s (Wg.lam (fun _ => ?wg''))

--//// Equivalence between source and Wg

namespace Den
-- maybe this can be easier if instead of using denotational semantics we use
-- operational and given an input we step from wg to wg instead of Den

inductive Equiv_den : {a:Type _} -> Den -> a -> Prop where
  | k :
    {b:Type _} ->
    (s:Felt -> b) ->
    (k:Felt -> Den) ->
    (∀ x, Equiv_den (k x) (s x)) ->
    Equiv_den (Den.input k) s
  | b :
    (s:Option Unit) ->
    Equiv_den (Den.bool s) s

inductive Equiv : {a:Type _} -> Wg' -> a -> Prop where
  | equiv :
    {a:Type _} ->
    (wg:Wg') ->
    (s:a) ->
    (Equiv_den (eval_wg' wg) s) ->
    Equiv wg s

notation : 65 t:65 "≡" s:66 => Equiv t s

example : ∃ wg':Wg', wg' ≡ eq0 := by
  refine ⟨?wg', ?heq⟩
  rotate_left
  apply Equiv.equiv
--  unfold eq0
  show Equiv_den (eval_wg' (fun var => Wg.lam (fun _:var => (?wg''' : Wg var)))) eq0
  unfold eq0
  simp only [eval_wg', eval_wg]
  apply Equiv_den.k
  intro x


example : ∃ wg':Wg', wg' ≡ nil := by
  refine ⟨?wg', ?heq⟩
  rotate_left
  apply Equiv.equiv
  show Equiv_den (eval_wg' (fun var => Wg.lam (fun _:var => (?wg'' : Wg var)))) nil
  unfold nil
  unfold eval_wg'
  unfold eval_wg
  have
  dsimp only [eval_wg', eval_wg]
  apply Equiv_den.k
  intro x
       Equiv_den (eval_wg (?m.17 Felt x)) (some ())
  show Equiv_den (eval_wg (fun var => Wg.lam (fun _:var => Wg.nil))) (some ())

  apply Equiv_den.b

  change Equiv_den (eval_wg' (fun var => Wg.lam (fun _:var => ?wg''))) (fun x => some ())
