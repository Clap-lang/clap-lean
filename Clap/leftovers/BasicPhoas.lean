set_option linter.unusedVariables true
set_option autoImplicit false

/-
-- if I use cases on the proof, after the proof is done, there is still an unsolved goal for x
example : ∃ (x:Option Nat), (x = some 5 ∨ x = none) := by
  refine ⟨?x, ?pf⟩
  rotate_left
  cases ?x with
    | none =>
      right; rfl
--      simp
    | some val =>
      left ; congr
  sorry
-/

/-
match on the goal
induction
Or use choose tactic or obtain pattern

    generalize ?arr' Felt = arr_felt

 exact match var with
    | _ => Arr.lam fun x => Arr.wg ?wg  -- ?wg becomes a new goal

    refine Equiv_arr.k ?s ?k ?h

-/

example : ∃ (x:Option Nat), (x = some 5 ∨ x = none) := by
  refine ⟨?x, ?pf⟩
  rotate_left
  left
  rfl


abbrev Felt := Int

inductive Exp (var:Type _) where
  | v : var -> Exp var
  | c : Felt -> Exp var
  | op : Exp var -> Exp var -> Exp var

def Exp' : Type _ := (var:Type _) -> Exp var

def eval_e (e: Exp Felt) : Felt :=
  match e with
  | Exp.v v => v
  | Exp.c i => i
  | Exp.op l r => eval_e l + eval_e r

def eval_e' (e:Exp') := eval_e (e Felt)

def equiv_e (t:Exp') (s:Felt) := eval_e (t Felt) = s

notation : 65 t:65 "≡" s:66 => equiv_e t s

-- /////////////////////

-- here we can add more types

inductive Wg (var:Type _) where
  | nil : Wg var
  | eq0 : Exp var -> Wg var -> Wg var
  | is_zero : Exp var -> (var -> Wg var) -> Wg var

def Wg' : Type _ := (var:Type _) -> Wg var

-- denotation of Wg is bool/M Unit

inductive Arr (var:Type _) where
  | wg : Wg var -> Arr var
  | lam : (var -> Arr var) -> Arr var

def Arr' : Type _ := (var:Type _) -> Arr var

abbrev M : Type 0 -> Type 0 := fun a => Option a

inductive Den_arr where
  | b : M Unit -> Den_arr
  | k : (Felt -> Den_arr) -> Den_arr

namespace Eval_fun
def eval_wg (wg:Wg Felt) : M Unit :=
  match wg with
  | Wg.nil => some ()
  | Wg.eq0 e wg =>
    if eval_e e = 0 then eval_wg wg else none
  | Wg.is_zero e k =>
    let b : Felt := if eval_e e = 0 then 1 else 0
    eval_wg (k b)

def eval_wg' (wg:Wg') : M Unit := eval_wg (wg Felt)

def eval_arr (arr:Arr Felt) : Den_arr :=
  match arr with
  | Arr.wg wg => Den_arr.b (eval_wg wg)
  | Arr.lam k => Den_arr.k (fun (x:Felt) => eval_arr (k x))

def eval_arr' (arr':Arr') : Den_arr := eval_arr (arr' Felt)

end Eval_fun



def eq0 (x:Felt) : M Unit :=
  if (x = 0) then some () else none

def eq0_arr : Arr' := fun var => Arr.lam (fun (x:var) => Arr.wg (Wg.eq0 (Exp.v x) Wg.nil))



inductive Equiv_arr : {a:Type 0} -> Den_arr -> a -> Prop where
  | k :
    {b:Type 0} ->
    (s:Felt -> b) ->
    (k:Felt -> Den_arr) ->
    (∀ x, Equiv_arr (k x) (s x)) ->
    Equiv_arr (Den_arr.k k) s
  | b :
    (s:M Unit) ->
    Equiv_arr (Den_arr.b s) s

namespace Func
inductive Equiv_func : {a:Type 0} -> Arr' -> a -> Prop where
  | equiv :
    {a:Type 0} ->
    (wg:Arr') ->
    (s:a) ->
    (Equiv_arr (Eval_fun.eval_arr' wg) s) ->
    Equiv_func wg s

notation : 65 t:65 "≡" s:66 => Equiv_func t s

namespace Crazy
def lemma (b:Type 0) (arr':Arr') (s:Felt -> b) :
  ∀ x, arr' ≡ rest x ->
  (fun var => Arr.lam (fun _:var => arr' var)) ≡ s := by
  intros equiv
  apply Equiv_func.equiv
  simp [Eval_fun.eval_arr]
  apply Equiv_arr.k
  intro x
  cases equiv -- not very nice
  assumption

def lemma (a:Type 0) (arr':Arr') (rest:a) :
  arr' ≡ rest ->
  (fun var => Arr.lam (fun _:var => arr' var)) ≡ (fun _:Felt => rest) := by
  intros equiv
  apply Equiv_func.equiv
  simp [Eval_fun.eval_arr]
  apply Equiv_arr.k
  intro x
  cases equiv -- not very nice
  assumption

example : ∃ arr':Arr', arr' ≡ eq0 := by
  refine ⟨?arr', ?heq⟩
  rotate_left
  change (fun var => Arr.lam (fun _:var => (?inner:Arr') var)) ≡ eq0
  apply lemma (Felt -> M Unit) ?inner eq0

end Crazy


example : ∃ arr':Arr', arr' ≡ eq0 := by
  refine ⟨?arr', ?heq⟩
  rotate_left
  show (fun var => Arr.lam (fun _:var => (?bla:Arr') var)) ≡ eq0
  apply Equiv_func.equiv
-- this simp ruins everything
  simp (config := {beta := false}) only [Eval_fun.eval_arr']
-- Equiv_arr (Eval_fun.eval_arr ((fun var => Arr.lam fun x => ?bla var) Felt)) eq0
  change Equiv_arr (Eval_fun.eval_arr (Arr.lam fun x => ?bla Felt)) eq0
  show Equiv_arr (Den_arr.k (fun x => Eval_fun.eval_arr (?bla Felt))) eq0



  refine Equiv_arr.k (fun x => ?s_body) (fun x => Eval_fun.eval_arr (?k x)) ?h


  apply Equiv_arr.k


  apply_rules (config := {beta := false} [Equiv_arr.k]
-- eq0_arr : Arr' := fun var => Arr.lam (fun (x:var) => Arr.wg (Wg.eq0 (Exp.v x) Wg.nil))

  refine Equiv_arr.k ?s ?k ?h

  apply {beta := false} Equiv_arr.k
  intro x
  simp [eq0]
  show Equiv_arr (Eval_fun.eval_arr (fun var => (fun (x:var) => fun var => Arr.wg (Wg.eq0 (Exp.v x) Wg.nil))) Felt x Felt) (if x = 0 then some () else none)
  show (fun var => Arr.lam (fun _:var => (?bla:Arr') var)) ≡ eq0


  change Equiv_arr (Eval_fun.eval_arr ((fun var => Arr.lam (fun _:var => (?bla:Arr') var)) Felt)) eq0


-- This worked
--  change Equiv_arr (Eval_fun.eval_arr ((fun var => ?arr) Felt)) eq0


  conv =>
  lhs
  arg 1
  change (fun var => Arr.lam (fun x => ?arr)) Felt

  change (fun var => Arr.lam (fun x => ?arr)) Felt

  change Equiv_arr (Eval_fun.eval_arr (?arr' Felt)) fun x => if x = 0 then some () else none
  unfold eq0
  change (fun var => Arr.lam (fun _:var => (?inner:Arr') var)) ≡ eq0



  change (fun var => Arr.lam (fun _:var => (?inner:Arr') var)) ≡ eq0
  apply lemma (Felt -> M Unit) ?inner eq0

  change (fun var => Arr.lam (fun _:var => ?inner)) ≡ eq0

  induction ?arr Felt with
  | lam k a_ih =>
    unfold Eval_fun.eval_arr
    apply Equiv_arr.k
    intro x

    cases (k x)
    case heq.a.lam.a.wg kwg => -- take a wg
      simp [Eval_fun.eval_arr]
      simp [eq0]
      apply Equiv_arr.b

    case heq.a.lam.a.wg kwg => -- take another k



  split
  case h_1 arr wg heq => sorry -- take a wg
  case h_2 arr k heq => -- take a arr
   unfold eq0
   apply Equiv_arr.k


end Func

-- ///////////////////////

namespace R

inductive eval_wg : Wg Felt -> M Unit -> Prop where
  | nil : eval_wg Wg.nil (some ())
  | eq0_false : (e:Exp Felt) -> (wg:Wg Felt) -> (eval_e e ≠ 0) -> eval_wg (Wg.eq0 e wg) none
  | eq0_true  : (e:Exp Felt) -> (wg:Wg Felt) -> (eval_e e = 0) -> (b:M Unit) -> eval_wg wg b -> eval_wg (Wg.eq0 e wg) b
  | is_zero
    (e:Exp Felt)
    (k:Felt -> Wg Felt)
    (b:M Unit)
    (arg:Felt)
    (h:(eval_e e = 0 → arg=1) ∧ (eval_e e ≠ 0 -> arg=0))
    (h2:eval_wg (k arg) b) :
    eval_wg (Wg.is_zero e k) b

inductive eval_arr : Arr Felt -> Den_arr -> Prop where
  | wg : (wg:Wg Felt) -> (b:M Unit) -> (eval_wg wg b) -> eval_arr (Arr.wg wg) (Den_arr.b b)
  | lam : (kwg:Felt -> Arr Felt) -> (k : Felt -> Den_arr) -> (∀ x, eval_arr (kwg x) (k x)) -> eval_arr (Arr.lam kwg) (Den_arr.k k)

-- inductive eval_arr': Arr' -> Den_arr -> Prop where
--  | wrap : (a:Arr') -> (d:Den_arr) -> eval_arr (a Felt) d -> eval_arr' a d

inductive Equiv_rel : {a:Type 0} -> Arr' -> a -> Prop where
  | equiv :
    {a:Type 0} ->
    (wg:Arr') ->
    (s:a) ->
    (d:Den_arr) ->
    (Eval_rel.eval_arr (wg Felt) d) ->
    (Equiv_arr d s) ->
    Equiv_rel wg s

notation : 65 t:65 "≡" s:66 => Equiv_rel t s

example : ∃ arr':Arr', arr' ≡ eq0 := by
  refine ⟨?arr', ?heq⟩
  rotate_left
  apply Equiv_rel.equiv
  rotate_left
  apply Equiv_arr.k ; intro
  apply Equiv_arr.b
  rotate_left
  apply Eval_rel.eval_arr'.wrap
  show Eval_rel.eval_arr ((fun var => ?k) Felt) (Den_arr.k fun x => Den_arr.b (eq0 x))

  apply Eval_rel.eval_arr.lam _ (fun x => Den_arr.b (eq0 x)) _

  show Eval_rel.eval_arr ((fun var => Arr.lam ?k) Felt) (Den_arr.k fun x => Den_arr.b (eq0 x))

  show Eval_rel.eval_arr ((fun var => Arr.lam (?k:var -> Arr var)) Felt) (Den_arr.k fun x => Den_arr.b (eq0 x))


  apply Eval_rel.eval_arr.lam

--   Eval_rel.eval_arr (Arr.lam ?kwg) (Den_arr.k ?k)
-- with the goal
--   Eval_rel.eval_arr (?arr' Felt) (Den_arr.k )


--   unfold eq0
--   rotate_left

-- def ex_cs : ∃ wg:Arr', wg ≡ ex_direct := by
--   apply Exists.intro
--   apply Equiv_rel.equiv
--   rotate_left
--   unfold ex_direct
--   apply Equiv_arr.k ; intro
--   apply Equiv_arr.b
--   rotate_left
--   apply Eval_rel.eval_arr.lam

end R



def lemma_bool : ∀ x, x * (1-x) = 0 <-> (x=0 ∨ x=1) := by sorry



-- this spec could be pure (even if its impl is not)
-- here we make it monadic to make ex more representative
def isZero (x:Felt) : M Felt :=
  some (if (x = 0) then 1 else 0)


def ex_direct (x:Felt) : M Unit := do
  let o <- isZero x
  eq0 o

def ex_bind (x:Felt) : M Unit :=
  bind (isZero x) (fun o => eq0 o)

def ex_unfold (x:Felt) : M Unit :=
  match (isZero x) with
  | some v => (fun o => eq0 o) v
  | none => none


def ex_wg {var} (x:var) : Wg var :=
  open Wg in
  let k : Wg var := nil
  let eq0 (o:var) : Wg var :=
    let e := Exp.op (Exp.v o) (Exp.c 1)
    eq0 e k
  let e := Exp.v x
  Wg.is_zero e eq0




example : ∃ wg:Arr', wg ≡ eq0 := by
  refine ⟨?arr, ?heq⟩
  rotate_left
  apply Equiv_func.equiv
  unfold Eval_fun.eval_arr
  induction (?arr Felt) with
  | lam k a_ih =>
    simp
    apply Equiv_arr.k
    intro x
    cases (k x)
    case heq.a.lam.a.wg wg =>
    simp [Eval_fun.eval_arr]
    simp [eq0]
    apply Equiv_arr.b
     sorry
  | wg wg => sorry

    apply Equiv_arr.b
    simp [Eval_fun.eval_arr]


  case heq.a.wg heq => -- take an arr
    refine (k x)

      simp [Eval_fun.eval_arr]
  case h_1 heq wg arr => -- stop arr, takea wg
    sorry

    rw [k]

apply Eval_fun.eval_arr
  apply Equiv_arr.b
  simp [Eval_fun.eval_arr]

  exact eq0_arr
end F


  -- repeat (first | simp [equiv_cs, sat] | apply eval_cs_eq0 | apply eval_cs_nil )
-- ////////////////////

inductive Cs (var:Type) where
  | nil : Cs var
  | eq0 : Exp var -> Cs var -> Cs var
  | lam : (var -> Cs var) -> Cs var

def Cs' : Type 1 := (var:Type 0) -> Cs var

inductive Denot where
  | k : (Felt -> Denot) -> Denot
  | b : Bool -> Denot

def eval_cs (cs:Cs Felt) : Denot :=
  match cs with
  | Cs.nil => Denot.b true
  | Cs.eq0 e cs => if eval_e e = 0 then eval_cs cs else Denot.b false
  | Cs.lam cs => Denot.k (fun f => eval_cs (cs f))

def eval_cs' (cs:Cs') : Denot := eval_cs (cs Felt)







-- ///////////////

-- inductive SDenot (a:Type) where
--   | some : a -> SDenot a
--   | none : SDenot a

/-
inductive M (a:Type) where
  | cont : (Felt -> M a) -> M a
  | none : M a
  | some : a -> M a

-- can we write a bind for the above?

def bind {a b:Type} (f:M a) (g:(x:a) -> M b) : M b :=
  match f with
  | M.none => M.none
  | M.some x => g x
  | M.cont k => M.cont (fun x => bind (k x) g)

-- what is this?!
-/
/-
instance : Monad M where
  pure a := M.some a
  bind m f := match m with
    | M.none
    | M.some x => m
    | MyMaybe.just a => f a


def isZero' (x:Felt) : m Int := -- spec is pure but impl is not
  if x = 0 then m.some 1 else m.some 0

def assert1' (x:Felt) : m Unit :=
  if x = 1 then m.some () else m.none

def ex' := m.cont (fun x =>
  bind (isZero' x) assert1')
-/
-- ///////////////////////

-- equiv should be a relation because it must be partial,

-- def Equiv_cs (s:Denot) (cs:Cs Felt) : Prop :=
--   match s, eval_cs cs with
--   | Denot.cont ks, Denot.cont kcs => ks = kcs -- funext
--   | Denot.bool bs, Denot.bool bcs => bs = bcs
--   | _,_ => False

-- inductive Equiv_f (f:Int -> Int) {a:Type} (s:a) where
--   | cont: (h:a = (Int -> Int)) -> (f = (h ▸ s)) -> Equiv_f f s

/-
notation : 65 t:65 "≡" s:66 => Equiv_cs t s

def eval_cs_nil : (fun _ => Cs.nil) ≡ sat [] := by
  simp [Equiv_cs, eval_cs, sat]

def eval_cs_eq0 (e:Exp') (cs:Cs') (z:Int) (zs:List Int):
  e ≡ z -> cs ≡ zs ->
  (fun var => Cs.eq0 (e var) (cs var)) ≡ z::zs := by
  intros he hcs
  simp [equiv_e, equiv_cs, sat] at he hcs
  simp [equiv_cs, eval_cs, sat] -- all_cons
  rewrite [he, hcs]
  simp

def ex_cs : ∃ cs:Cs', cs ≡ [0] := by
  apply Exists.intro
  repeat (first | simp [equiv_cs, sat] | apply eval_cs_eq0 | apply eval_cs_nil )

def ex_cs' : ∃ cs:Cs', cs ≡ [1+2,3+6] := by
  apply Exists.intro
  repeat (first
    | apply eval_cs_eq0 ; repeat (first | apply eval_op | apply eval_c )
    | apply eval_cs_nil)

def parse_cs (s:List Int) : ∃ cs:Cs', cs ≡ s := by
  induction s with
  | nil =>
    apply Exists.intro
    apply eval_cs_nil
  | cons hd tl ih =>
    let ⟨?_,p⟩ := ih;
    apply Exists.intro
    apply eval_cs_eq0
    repeat (first | apply eval_op | apply eval_c )
    apply p
-/
