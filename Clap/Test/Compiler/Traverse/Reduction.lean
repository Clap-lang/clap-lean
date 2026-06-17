import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

def testbetaReduction : Option ℕ := do
  let a ← (λ x y => .some (x - y)) 1 2
  return a

def f (a b: Unit): Unit := a
def g := λ a b => f a b

#check Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.lam
      `x
      (Lean.Expr.const `Nat [])
      (Lean.Expr.lam
        `y
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHSub [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instSubNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.lit (Lean.Literal.natVal 1)))
      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
      (Lean.Expr.lit (Lean.Literal.natVal 2)))
    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 2))))

-- set_option trace.Clap.Compile true in
-- set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
set_option maxRecDepth 100000 in
#eval runTestByName ``testbetaReduction

end NewTraversal

end ExampruSym
