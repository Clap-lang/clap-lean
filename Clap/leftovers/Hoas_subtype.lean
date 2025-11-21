set_option autoImplicit false
set_option linter.unusedVariables true

namespace Phoas

abbrev Felt := Int

inductive Exp where
  | c : Felt -> Exp
  | op : Exp -> Exp -> Exp

def eval_e (e: Exp) : Felt :=
  match e with
  | Exp.c i => i
  | Exp.op l r => eval_e l + eval_e r

inductive Circuit where
  | nil : Circuit
  | eq0 : Exp -> Circuit -> Circuit
  | lam : (Exp -> Circuit) -> Circuit
  | share : Exp -> (Exp -> Circuit) -> Circuit
  | is_zero : Exp -> (Exp -> Circuit) -> Circuit

def is_cs (c:Circuit) : Prop :=
  open Circuit in
  match c with
  | nil => true
  | eq0 _ c => is_cs c
  | lam k => ∀ (x:Exp), is_cs (k x)
  | _ => false

def Cs := { c:Circuit // is_cs c }

namespace Functional
namespace Circuit

def eval (c:Circuit) : Option Circuit :=
  match c with
  | Circuit.nil
  | Circuit.lam _ => some c
  | Circuit.eq0 e c =>
    if eval_e e = 0 then eval c else none
  | Circuit.share e k => eval (k e)
  | Circuit.is_zero e k =>
    if eval_e e = 0 then eval (k (Exp.c 1)) else eval (k (Exp.c 0))

end Circuit

inductive s_bisim : (l r: Option Circuit) -> Prop where
  | false
      : s_bisim none none
  | true
      : s_bisim (some .nil) (some .nil)
  | sync
      (kl kr:Exp -> Circuit)
      (h: ∀ x, s_bisim (Circuit.eval (kl x))
                       (Circuit.eval (kr x)))
      : s_bisim (some (.lam kl)) (some (.lam kr))

inductive rw_bisim : (l r: Option (Circuit)) -> Prop where
  | false
      : rw_bisim none none
  | true
      : rw_bisim (some .nil) (some .nil)
  | sync
      (kl kr:Exp -> Circuit)
      (h: ∀ x, s_bisim (Circuit.eval (kl x))
                       (Circuit.eval (kr x)))
      : rw_bisim (some (.lam kl)) (some (.lam kr))
  | async
      (l:Circuit)
      (kr:Exp -> Circuit)
      (x:Exp)
      (h: rw_bisim l (Circuit.eval (kr x)))
      : rw_bisim l (some (.lam kr))

namespace Gen_trace

-- replacing felt with exp would simplify
-- a list with continuations
inductive Wg where
  | nil : Wg
  | cons : Felt -> Wg -> Wg
  | input : (Felt -> Wg) -> Wg

def to_wg (c:Circuit) : Wg :=
  match c with
  | Circuit.nil => Wg.nil
  | Circuit.eq0 _ c => to_wg c
  | Circuit.lam k => Wg.input (fun i => to_wg (k (Exp.c i)))
  | Circuit.share e k =>
    Wg.cons (eval_e e) (to_wg (k e))
  | Circuit.is_zero e k =>
    let e := if eval_e e = 0 then Exp.c 1 else Exp.c 0
    Wg.cons (eval_e e) (to_wg (k e))

def wrap (cs:Cs) (gt:Wg) : Cs :=
  let ⟨c,p⟩ := cs
  match c with
  | .nil => cs
  | .eq0 e c =>
    let ⟨c,p⟩ := wrap ⟨c, by simp [is_cs] at p ; apply p ⟩ gt
    ⟨.eq0 e c, p⟩
  | .lam k =>
    match gt with
    | Wg.nil => ⟨.nil, by simp [is_cs]⟩
    | Wg.cons x gt =>
      wrap ⟨k (Exp.c x), by simp [is_cs] at p ; apply p ⟩ gt
    | Wg.input k_gt =>
      let c := Circuit.lam (fun x =>
        let cs := ⟨(k x), by simp [is_cs] at p; apply p⟩
        let ⟨c,_⟩ := wrap cs (k_gt (eval_e x))
        c)
      ⟨c, by
  unfold c
  unfold is_cs at p
  unfold is_cs
  simp;

end Gen_trace

-- let's derive this as an existential from bisim
def to_cs (c:Circuit) : Cs :=
  match c with
  | Circuit.nil => Cs.nil
  | Circuit.eq0 e c => Cs.eq0 e (to_cs c)
  | Circuit.lam k => Cs.lam (fun x => to_cs (k x))
  --
  | Circuit.share e k =>
      Cs.lam (fun o =>
        Cs.eq0 (Exp.op e o) (to_cs (k o)))
  | Circuit.is_zero e k =>
    Cs.lam (fun inv =>
      Cs.lam (fun o =>
        Cs.eq0 (Exp.op e (Exp.op o inv)) (to_cs (k o))))

theorem soundness : ∀ (c:Circuit), Functional.rw_bisim c (to_cs c) :=
  sorry

def completeness : ∀ (c:Circuit),
  Functional.s_bisim c (Gen_trace.wrap (to_cs c) (Gen_trace.to_wg c)) := sorry

def unshare (pos:Nat) (c:Circuit) : Circuit :=
  match c with
  | .nil => c
  | .eq0 e c => .eq0 e (unshare pos c)
  | .lam k => .lam (fun x => unshare pos (k x))
  | .is_zero e k => .is_zero e (fun x => unshare pos (k x))
  --
  | .share e k =>
    if pos = 0 then k e
    else .share e (fun x => unshare (pos-1) (k x))
