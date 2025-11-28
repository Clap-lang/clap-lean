import Clap.Circuit
open Circuit

def enforce_binary {var} (e:var) (rest:Circuit var) : Circuit var :=
  eq0 (.v e * (.c 1 - .v e)) rest

def rangeCheck256 {var} (a:var) (bs : Vector var 8) (rest:Circuit var) : Circuit var :=
  let rest := Vector.foldl (fun acc b => enforce_binary b acc) rest bs
  eq0 ((.c 128 * .v bs[0]) +
       (.c  64 * .v bs[1]) +
       (.c  32 * .v bs[2]) +
       (.c  16 * .v bs[3]) +
       (.c   8 * .v bs[4]) +
       (.c   4 * .v bs[5]) +
       (.c   2 * .v bs[6]) +
       (.c   1 * .v bs[7]) - .v a) rest

example : Circuit' := fun _var =>
          lam (fun a =>
          lam (fun b0 =>lam (fun b1 => lam (fun b2 =>lam (fun b3 =>
          lam (fun b4 =>lam (fun b5 => lam (fun b6 =>lam (fun b7 =>
            rangeCheck256 a ⟨#[b0,b1,b2,b3,b4,b5,b6,b7],rfl⟩ nil)))))))))
