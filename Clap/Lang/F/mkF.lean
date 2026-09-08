import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

def mkF (a : ZMod p) : ClapM p F :=
  HashConsM.mkConstant (p := p) a

namespace mkF

@[simp]
lemma hashConsM_convertsM
  {state}
  {x : ZMod p}
:
  ConvertsM F.conversion (liftM (HashConsM.mkConstant (p := p) x)) state x True
:= by
  constructor
  · simp [ClapM.getState]
    simp_rw [HashConsM.getResult_mkConstant, HashConsM.getHashConsState_mkConstant]
    constructor <;> simp
    · grind [=Expr.varSet, =Expr.varSet_wellFormed]
    · grind
    · rw [eval_eq_evalRec (by grind)]
      grind
  · grind
  . grind [ClapM.runAndEval]

lemma convertsM
  {state : ClapMState p}
  {a : ZMod p}
:
  ConvertsM F.conversion (mkF a) state a True
:= hashConsM_convertsM

end mkF

end Clap.Lang
