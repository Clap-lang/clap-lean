import Clap.Phoas

set_option autoImplicit false
set_option linter.unusedVariables true

namespace Relational
-- no need for option
/-
namespace Circuit
inductive eval : Circuit F -> Circuit F -> Prop where
  | nil : eval Circuit.nil Circuit.nil
  | lam
      (k:F -> Circuit F)
      : eval (Circuit.lam k) (Circuit.lam k)
  | eq0_t
      (e:Exp F)
      (c:Circuit F)
      (h:eval_e e = 0)
      : eval (Circuit.eq0 e c) c
  | is_zero
      (e:Exp F)
      (k:F -> Circuit F)
      (b:F)
      (h:(eval_e e = 0 → b=1) ∧ (eval_e e ≠ 0 -> b=0))
      : eval (Circuit.is_zero e k) (k b)

end Circuit

namespace Cs
-- relational, no need for option
inductive eval : Cs F -> Cs F -> Prop where
  | nil : eval Cs.nil Cs.nil
  | lam
      (k:F -> Cs F)
      : eval (Cs.lam k) (Cs.lam k)
  | eq0_t
      (e:Exp F)
      (cs:Cs F)
      (h:eval_e e = 0)
      : eval (Cs.eq0 e cs) cs
end Cs

inductive s_bisim : (l: Circuit F) -> (r: Cs F) -> Prop where
  | true
      : s_bisim Circuit.nil Cs.nil
  | sync
      (kl:F -> Circuit F)
      (kr:F -> Cs F)
      (lres:Circuit F)
      (rres:Cs F)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Cs.eval (kr x) rres) ->
        s_bisim lres rres)
      : s_bisim (Circuit.lam kl) (Cs.lam kr)

def s_bisim' (l : Circuit') (r : Cs') := s_bisim (l F) (r F)

inductive rw_bisim : (l: Circuit F) -> (r: Cs F) -> Prop where
  | true
      : rw_bisim Circuit.nil Cs.nil
  | sync
      (kl:F -> Circuit F)
      (kr:F -> Cs F)
      (lres:Circuit F)
      (rres:Cs F)
      (h: ∀ x,
        (hl: Circuit.eval (kl x) lres) ->
        (hr: Cs.eval (kr x) rres) ->
        rw_bisim lres rres)
      : rw_bisim (Circuit.lam kl) (Cs.lam kr)
  | async
      (l:Circuit F)
      (kr:F -> Cs F)
      (rres:Cs F)
      (x:F) -- ∃ x
      (h: Cs.eval (kr x) rres -> rw_bisim l rres)
      : rw_bisim l (Cs.lam kr)

def rw_bisim' (l : Circuit') (r : Cs') := rw_bisim (l F) (r F)

-/
end Relational
