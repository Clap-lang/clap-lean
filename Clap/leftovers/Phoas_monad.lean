import Mathlib.Control.Monad.Cont
import Clap.Circuit

set_option autoImplicit false
set_option linter.unusedVariables true

open Circuit

namespace Phoas_monad

abbrev C var a := Cont (Circuit var) a

def lam {var} : C var var := fun k =>
  Circuit.lam k

def eq0 {var} (e:Exp var) : C var Unit := fun k =>
  Circuit.eq0 e (k ())

def share {var} (e:Exp var) : C var var := fun k =>
  Circuit.share e k

def is_zero {var} (e:Exp var) : C var var := fun k =>
  Circuit.is_zero e k

example {var} : C var Unit := do
  let i <- lam
  eq0 (.v i)

def unshare_e {var} (e:Exp (Exp var)) : Exp var :=
  match e with
  | .v v => v
  | .c f => .c f
  | .add l r => .add (unshare_e l) (unshare_e r)
  | .mul l r => .mul (unshare_e l) (unshare_e r)
  | .sub l r => .sub (unshare_e l) (unshare_e r)

def degree {var} (e:Exp var) : Nat :=
  match e with
  | .v _ => 1
  | .c _ => 0
  | .add l r
  | .sub l r => max (degree l) (degree r)
  | .mul l r => (degree l) + (degree r)

def unshare_deg {var} (c:Circuit (Exp var)) : Cont (Circuit var) (Bool × Circuit var) :=
  match c with
  | .nil => pure (true,.nil)
  | .eq0 e c => do
     let be := degree e <= 2
     let (b,c) <- unshare_deg c
     pure (b && be, .eq0 (unshare_e e) c)
  | .lam k' =>
     .lam (fun x => unshare_deg (k' (.v x)))
  | .is_zero e k' =>
     let be := degree e <= 2
    .is_zero (unshare_e e) (fun x => unshare_deg (k' (.v x)) (fun (b,c) => k (b && be, c)))
  --
  | .share e k' =>
     let be := degree e <= 2
     unshare_deg (k' (unshare_e e)) (fun (b,c) =>
       if b && be
       then k (true, c)
       else .share (unshare_e e) (fun x => unshare_deg (k' (.v x)) k))

end Phoas_monad
