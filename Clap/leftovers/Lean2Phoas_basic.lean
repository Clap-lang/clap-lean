namespace Basic

-- set_option aesop.check.all true
-- declare_aesop_rule_sets [Basic.A]

-- set_option trace.aesop true

inductive Exp where
  | c : Int -> Exp
  | op : Exp -> Exp -> Exp

def eval_e (e: Exp) : Int :=
  match e with
  | Exp.c i => i
  | Exp.op l r => eval_e l + eval_e r

def equiv_e (t:Exp) (s:Int) := eval_e t = s

notation : 65 t:65 "≡" s:66 => equiv_e t s

-- @[aesop safe [(rule_sets := [Basic.A])]]
def eval_c (n:Int) : Exp.c n ≡ n := by
  simp [equiv_e, eval_e]

def eval_op (el er:Exp) (l r:Int) :
  el ≡ l → er ≡ r →
  Exp.op el er ≡ (l + r) := by
  intros hl hr;
  simp [equiv_e] at hl hr
  simp [equiv_e, eval_e, *]

def a_manual : ∃ e:Exp, e ≡ (1+2) := by
  apply Exists.intro
  apply eval_op
  apply eval_c
  apply eval_c

def a : ∃ e:Exp, e ≡ (1+2) := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )

-- #print a_aesop
-- Exists.intro (Exp.c (1 + 2)) (eval_c (1 + 2))
-- We should first apply op then c

-- This is only partially true, because we can always reduce an expression into an Int, but we won't be producing the AST that we really want.
def parse_e (s:Int) : ∃ e:Exp, e ≡ s := by
  apply Exists.intro
  repeat (first | apply eval_op | apply eval_c )


inductive Cs where
  | nil : Cs
  | eq0 : Exp -> Cs -> Cs

def eval_cs (cs:Cs) : Bool :=
  match cs with
  | Cs.nil => true
  | Cs.eq0 e cs => if eval_e e = 0 then eval_cs cs else false

def sat (es:List Int) : Bool := List.all es (fun e => e = 0)

def equiv_cs (t:Cs) (s:List Int) := eval_cs t = sat s

notation : 65 t:65 "≡" s:66 => equiv_cs t s

def eval_cs_nil : Cs.nil ≡ [] := by
  simp [equiv_cs, eval_cs, sat]

def eval_cs_eq0 (e:Exp) (cs:Cs) (z:Int) (zs:List Int):
  e ≡ z -> cs ≡ zs ->
  Cs.eq0 e cs ≡ z::zs := by
  intros he hcs
  simp [equiv_e, equiv_cs, sat] at he hcs
  simp [equiv_cs, eval_cs, sat] -- all_cons
  rewrite [he, hcs]
  simp

def ex_cs : ∃ cs:Cs, cs ≡ [0] := by
  apply Exists.intro
  repeat (first | simp [equiv_cs, sat] | apply eval_cs_eq0 | apply eval_cs_nil )

def ex_cs' : ∃ cs:Cs, cs ≡ [1+2,3+6] := by
  apply Exists.intro
  repeat (first
    | apply eval_cs_eq0 ; repeat (first | apply eval_op | apply eval_c )
    | apply eval_cs_nil)

def parse_cs (s:List Int) : ∃ cs:Cs, cs ≡ s := by
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

end Basic
