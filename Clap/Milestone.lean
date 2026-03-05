import Clap.Lang
import Clap.Compiler.Basic
import Clap.Cfold
import Clap.Compilation
import Clap.Quadratic
import Clap.Sha2.Circuit
import Clap.BackEndFirstOrder


open Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

-- TODO we could make eq0 cps

def Cid {var} : Circuit p var → Circuit p var
  | .nil => .nil
  | .eq0 e c => .eq0 e (Cid c)
  | .lam k => .lam fun x ↦ Cid (k x)
  | .is_zero e k => .is_zero e fun x ↦ Cid (k x)
  | .share e k => .share e fun x ↦ Cid (k x)
  | .num2bits w e k => .num2bits w e fun x ↦ Cid (k x)

def Cid' (c:Circuit' p) : Circuit' p := fun var => Cid (c var)

def Cid2 {var} : Circuit p var → Cs p var
  | .nil => .nil
  | .eq0 e c => .eq0 e (Cid2 c)
  | .lam k => .lam fun x ↦ Cid2 (k x)
  | .is_zero e k
  | .share e k
  | .num2bits w e k => .nil

def Cid2' (c:Circuit' p) : Cs' p := fun var => Cid2 (c var)

-- def idCps {var} {res:Type} (c:Circuit p var) (k:Circuit p var -> res) : res :=
--   match c with
--   | .nil => k .nil
--   | .eq0 e c => idCps c fun c => k (.eq0 e c)
--   | .lam k' => k (.lam fun x => idCps (k' x) id)
--   | .share e k' => k (.share
--   -- | .is_zero e k' => fun c => idCps (k' ) .is_zero e fun x ↦ Cid (k x)
--   -- | .num2bits w e k => .num2bits w e fun x ↦ Cid (k x)
--   | _ => k .nil

-- #eval idCps (p:=Primes.goldilocks) (var:=ℕ) (
--   .lam fun x =>
--   .lam fun y =>
--   .eq0 (.v x) (
--   .eq0 (.v y)
--   .nil)) id

--def Cid' (c:Circuit' p) : Circuit' p := fun var => Cid (c var)

-- #eval! ((Cid' test_circ) ℕ)


def mkEq0 (p n:ℕ): Circuit' p := fun _var =>
  List.foldr (fun _ acc => .eq0 (.c 0) acc) .nil [0:n].toList

--#eval ((Cid' (mkEq0 Primes.babybear 3000)) ℕ)

def mkLam (p n:ℕ): Circuit' p := fun _var =>
  List.foldr (fun _ acc => .lam fun _ => acc) .nil [0:n].toList

def mkLamExp (p n:ℕ): Circuit' p := fun var =>
  let rest : Circuit p var := .eq0 (.c 1 + .c 2) .nil
  List.foldr (fun _ acc => .lam fun _ => acc) rest [0:n].toList

--#eval ((Cid' (mkLam Primes.babybear 5000)) ℕ)

open Primes
open Clap
open Lang

/-
  We assume the existance of a p, prime, that fits a number up 32 bits,
-/
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 32)]

/-
  We assume for that p, we have an instance of our Core subset
-/
variable [Core p]

open Core

-- structure MyCouple (p:ℕ) [Core p] where
--   x : F (p:=p)
--   y : F (p:=p)

-- def test (xy : MyCouple p) : Option Unit := do
--   eq0 xy.x
--   eq0 xy.y
--   F.assert_eq xy.x xy.y
--   accept p

-- def test {p:ℕ} [Core p] [Fact (Primes.fits p 32)]
--   (x y z : Vector (FB p) 32) : Option Unit := do
--   let x : F32 p := x.toList
--   let y : F32 p := y.toList
--   let z : F32 p := z.toList
--   F32.assert_eq (Clap.Sha2.Circuit.ch x y z) F32.default
--   -- accept p

def assert_eq (a b : List (F p)) : Option Unit :=
  match a,b with
  | [],[] => some ()
  | ha::tla,hb::tlb => do
      F.assert_eq ha hb
      assert_eq tla tlb
  | _,_ => none

def test {p:ℕ} [Core p] [Fact (Primes.fits p 32)]
  (x y z : Vector (F p) 1) : Option Unit := do
  let x := x.toList
  let y := y.toList
  let z := z.toList
  let ch : List (F p) := List.map (fun ((x,y),z) => x * (y - z) + z) ((x.zip y).zip z)
  assert_eq ch [0]
  -- accept p

-- def test (x y : F p) : Option Unit := do
--   let e := 5 * x - 3+1
--   F.assert_eq e y
--   accept p

-- def test (x y : F p) : Option Unit := do
--   let xs := F32.ofF x
--   let ys := F32.ofF y
--   let res := F32.add xs ys
--   F32.assert_eq F32.default res
--   accept p

-- def test3 (x : F p) : Option Unit := do
--   let xs := isZero x
--   FB.assert_eq xs FB.true
--   accept p

open Clap.Lang.ZMod

#compile test using Primes.goldilocks

-- /- The compiler gives us a circuit that we can compile further. -/
def test_circ : Circuit' goldilocks := test_ser

set_option pp.deepTerms true
set_option format.indent 0

#print test_ser

--#eval! (test_circ ℕ)

-- /- But also a wg_wrap which we can use to wrap our witness generator. -/
-- def test_wg_wrap -- : Wg bn254 -> MyCouple bn254 -> Array (ZMod bn254)
-- := test_ser_wg

-- /- We can optimize the circuit. -/
-- def test_circ_opt := Clap.cfold' test_circ


/- Compile the circuit to a cs. -/
--def test_cs : Cs' bn254 := Clap.toCs' test_circ

/- Compile the circuit to a cs. -/
-- def test_cs : FirstOrder.Cs bn254 := FirstOrder.toCs (test_circ ℕ) 0

-- #eval! test_cs

-- /- Compile the circuit to a wg. -/
-- def test_wg_raw : Clap.Wg bn254 := Clap.toWg' test_circ
-- /- And use the wrapper to get nicer arguments. -/
-- def test_wg -- : MyCouple bn254 → Array (ZMod bn254)
-- := test_wg_wrap (Clap.toWg' test_circ)

-- /- Serialize the cs to r1cs -/
-- def r1cs : R1CSv1 := quadraticToR1CS (Clap.toLevels test_cs)

def main (args : List String) : IO UInt32 := do
  IO.println s!"snarkjs ri {args[0]!}"
  -- let c := (Cid' (mkEq0 Primes.babybear 100)) ℕ
  -- if s!"{c}" = "" then return 1 else

  -- 100000 works
  -- let c := (Clap.toCs' (mkLam Primes.babybear 100000)) ℕ
  -- if s!"{c}" = "" then return 1 else

  -- let c := (Clap.toCs' (mkLamExp Primes.babybear 1000)) ℕ
  -- if s!"{c}" = "" then return 1 else

  let test_cs : Cs' goldilocks := Clap.toCs' test_ser
  if s!"{test_cs ℕ}" = "" then return 1 else
  return 0
