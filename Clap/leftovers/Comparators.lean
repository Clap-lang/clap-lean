import Clap.Circuit

set_option autoImplicit false
set_option linter.unusedVariables true

namespace Binsum

def bin_sum (n:Nat) (e:F) : Vector F n :=
  sorry

end Binsum

namespace Bitify

def num2bits (n:Nat) (e:F) : Vector F n :=
  sorry

end Bitify

namespace Comparators

def is_zero_spec (e:F) : F :=
  if e = 0 then 1 else 0

def is_zero_imp {var} (e:Exp var) : Circuit var :=
  .is_zero e (fun x => rest)

def spec : denotation := .l (fun e =>
  let _a := is_zero_spec e
  .u)

example : ∃ (c:Circuit'), eval' c = spec := by
  refine ⟨?c,?h⟩
  case' h =>
 -- refine eval' (fun _ => ?w)
  unfold eval'
  show eval ((fun _ => ?_) F) = spec
  simp [spec,eval',eval]

  refine
--  simp [eval']


  refine eval ((fun _ => ?w) F) = denotation.l fun e => denotation.u

 have h: ?c = (fun var => (?w : Circuit var)) := sorry
  rw [h]
 refine match ?w with
  | (fun _ => ?_ ) =>


def is_equal (e1 e2:F) : F :=
  is_zero (e1 - e2)

--def less_than (e1 e2:F) : F :=
  -- num2bits
  -- bin_sum

end Comparators
