import Clap.Circuit
import Clap.Compilation

namespace Clap.FirstOrder

variable {p : ℕ} [Fact (Nat.Prime p)]

inductive Cs (p : ℕ) : Type where
  | nil
  | eq0 (_ : Exp p ℕ) (_ : Cs p)
  | lam (_ : ℕ) (_ : Cs p)

def assert_bits_e (bs : List ℕ) (rest : Cs p) : Cs p :=
  List.foldr assert_bit_e rest bs
where
  assert_bit_e (b : ℕ) (rest : Cs p) : Cs p :=
    .eq0 (.v b * (.c 1 - .v b)) rest

-- TODO still not tail-recursive
def toCs (c : Circuit p ℕ) (fresh : ℕ) : Cs p :=
  match c with
  | .nil =>
      .nil
  | .eq0 e c =>
      .eq0 e (toCs c fresh)
  | .lam k =>
      let fresh := fresh+1
      .lam fresh (toCs (k fresh) fresh)
  | .share e k =>
      let o := fresh
      let fresh := fresh+1
      .lam o (.eq0 (e - .v o) (toCs (k o) fresh))
  | .is_zero e k =>
      let inv := fresh
      let o := fresh+1
      let fresh := fresh+2
      .lam inv (
      .lam o (
      .eq0 (.c 1 - .v inv * e - .v o) (
      .eq0 (.v o * e) (toCs (k o) fresh))))
  | .num2bits w e c =>
      let bits := [fresh:fresh+w].toList
      let fresh := fresh+w
      let rest : Cs p := toCs (c bits) fresh
      let rest : Cs p := .eq0 (Clap.bits2num_e bits - e) rest
      assert_bits_e bits rest

end Clap.FirstOrder
