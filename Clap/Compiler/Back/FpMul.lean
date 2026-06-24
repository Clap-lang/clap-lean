import CompPoly.Univariate.Basic

import Clap.Compiler.Back.Cs
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Wg

open Clap

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

namespace Clap.FpMul

section Circuit

def range_check_vec_circuit {k : ℕ} (w : ℕ) (vec : Vector (Exp p var) k) (rest : Cs p var) : Cs p var :=
  List.foldr (fun i r => Num2Bits.num2bits_circuit w vec[i] (fun _ ↦ r)) rest (List.finRange k)

def eval_poly {k : ℕ} (coeffs : Vector (Exp p var) k) (x : ZMod p) : Exp p var :=
  (List.finRange k).foldr
    (fun ind acc => acc + coeffs[ind] * .c (x ^ ind.1)) (.c 0)

def assert_poly_eq_prod {k : ℕ}
    (a : Vector (Exp p var) k)
    (b : Vector (Exp p var) k)
    (c : Vector (Exp p var) (2*k - 1))
    (rest : Cs p var) : Cs p var :=
  List.foldr
    (fun k rest =>
      Cs.eq0 ((eval_poly a k) * (eval_poly b k) - (eval_poly c k)) rest
    )
    rest
    (List.range (2*k - 1))

def check_carry_zero_circuit {k : ℕ} (n : ℕ) (t : Vector (Exp p var) k) (rest : Cs p var) : Cs p var :=
  if h : k = 0 then rest
  else
    Cs.curry (k - 1)
      (
        fun carry =>
          List.foldr
            (fun (i : Fin (k - 1)) rest =>
              let e :=
                if h : i.1 = 0
                then t[i]
                else
                  t[i] + (.v carry[(⟨i.1 - 1, by omega⟩ : Fin k)])
              Cs.eq0 (e - ((.c (2 ^ n)) * (.v carry[i])))
              (
                -- -(2 ^ (2*n + 1) * k) < - (2^(2*n)*k + 2^n)  < t[i] < (2 ^ (2 * n) * k) →
                -- 0 ≤ t[i] + (2 ^ (2*n + 1) * k) < (2 ^ (2 * n) * k) + (2 ^ (2*n + 1) * k) =
                -- (2 ^ (2 * n) * k) + (2 * 2 ^ (2 * n) * k) = 3 * (2 ^ (2 * n) * k) < 4 * (2 ^ (2 * n) * k) =
                -- 2 ^ (2 * n + 2) * k < 2 ^ (2 * n + Nat.clog 2 k + 2)
                Num2Bits.num2bits_circuit (n + Nat.clog 2 k + 2) (.v carry[i] + .c (2 ^ (n + 1) * k)) (fun _ ↦ rest)
              )
            )
            (
              Cs.eq0
                (
                  t[(⟨k - 1, by omega⟩ : Fin k)] +
                  (if h' : k = 1 then .c 0 else .v carry[(⟨k - 2, by omega⟩ : Fin (k - 1))])
                )
                rest
            )
            (List.finRange (k - 1))
      )

def check_lt_circuit' {k : ℕ} (w : ℕ) (isLt : Exp p var) (t₀ : Vector (Exp p var) k) (t₁ : Vector (Exp p var) k) (cont : Cs p var) : Cs p var :=
  match k with
  | .zero => .eq0 (isLt - 1) cont
  | .succ k =>
    -- Process the MSB (highest index `k`), then recurse on the first `k` elements
    -- (which drops the MSB via `i.castSucc`). This walks from MSB to LSB so that
    -- each position is visited exactly once.
    Num2Bits.num2bits_circuit w (t₀[Fin.last k] - t₁[Fin.last k] + (.c ((2 ^ w : ZMod p) - 1)))
      (fun _ ↦
        IsZero.isZero_circuit (t₀[Fin.last k] - t₁[Fin.last k])
        (fun iz ↦
          let isLt' : Exp p var :=
            isLt ||| (1 - .v iz)
          check_lt_circuit' w isLt' (Vector.ofFn (fun i ↦ t₀[(i.castSucc)])) (Vector.ofFn (fun i ↦ t₁[(i.castSucc)])) cont
        )
      )

def check_lt_circuit {k : ℕ} (w : ℕ) (t : Vector (Exp p var) k) (t' : Vector (Exp p var) k) (cont : Cs p var) : Cs p var :=
    check_lt_circuit' w 0 t t' cont

def fpMul_circuit {k : ℕ} (w : ℕ) (a b p' : Vector (Exp p var) k) (cont : Vector var k → Cs p var) : Cs p var :=
  range_check_vec_circuit w a $
      range_check_vec_circuit w b $
        range_check_vec_circuit w p' $
          Cs.curry (2 * k - 1)
            (fun ab ↦
              let ab : Vector (Exp p var) (2 * k - 1) := ab.map (.v)
              assert_poly_eq_prod a b ab
                (Cs.curry k
                  (fun q ↦
                    let q : Vector (Exp p var) k := q.map (.v)
                    range_check_vec_circuit w q $
                      Cs.curry k
                      (fun r ↦
                        let r' : Vector (Exp p var) k := r.map (.v)
                        range_check_vec_circuit w r' $
                          Cs.curry (2*k - 1)
                          (fun t ↦
                            let t : Vector (Exp p var) (2*k - 1) := t.map (.v)
                            List.foldr
                              (fun i ↦ Cs.eq0 (eval_poly t i - (eval_poly ab i - ((eval_poly p' i) * (eval_poly q i) + eval_poly r' i))))
                              (
                                check_carry_zero_circuit w t
                                  (
                                    check_lt_circuit w (r.map .v) p'
                                      (cont r)
                                  )
                              )
                              (List.range (2*k - 1))
                          )
                      )
                  )
                )
            )

end Circuit

section Wg

open CompPoly Clap

def range_check_vec_wg {k : ℕ} (w : ℕ) (vec : Vector (Exp p (ZMod p)) k) (rest : Wg p) : Wg p :=
  Vector.foldr (fun e wg ↦ Num2Bits.num2bits_wg w e (fun _ ↦ wg) ) rest vec

def toCompPoly {k : ℕ} (vec : Vector (ZMod p) k) : CPolynomial (ZMod p) :=
  List.foldr (fun i p ↦ p + CPolynomial.C (vec[i]) * CPolynomial.X ^ i.1) 0 (List.finRange k)

def carry (w : ℕ) : List (ZMod p) → ZMod p → List (ZMod p)
| l :: l' :: ls, c =>
  let c' : ZMod p := (l + c) / (2 ^ w)
  c' :: carry w (l' :: ls) c'
| _ :: [], _ => []
| [], _ => []

def check_carry_zero_wg {k : ℕ} (w : ℕ) (t : Vector (Exp p (ZMod p)) k) (rest : Wg p) : Wg p :=
  let carry : List (ZMod p) := carry w (t.toList.map Exp.eval) 0
  List.foldr
    Wg.cons
    (
      List.foldr
      (fun c rest ↦ Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2) (.c $ c + (2 ^ (w + 1) * k)) (fun _ ↦ rest))
      rest
      carry
    )
    carry

def check_lt_wg' {k : ℕ} (w : ℕ) (isLt : Expₑ p) (t₀ : Vector (Expₑ p) k) (t₁ : Vector (Expₑ p) k) (cont : Wg p) : Wg p :=
  match k with
  | .zero => cont
  | .succ k =>
    Num2Bits.num2bits_wg w (t₀[Fin.last k] - t₁[Fin.last k] + (Exp.c ((2 ^ w : ZMod p) - 1)))
      (fun _ ↦
        IsZero.isZero_wg (t₀[Fin.last k] - t₁[Fin.last k])
          (fun iz ↦
            let isLt' : Expₑ p :=
              isLt ||| (1 - .v iz)
            check_lt_wg' w isLt' (Vector.ofFn (fun i ↦ t₀[(i.castSucc)])) (Vector.ofFn (fun i ↦ t₁[(i.castSucc)])) cont
          )
      )

def check_lt_wg {k : ℕ} (w : ℕ) (t : Vector (Expₑ p) k) (t' : Vector (Expₑ p) k) (cont : Wg p) : Wg p :=
  check_lt_wg' w 0 t t' cont

def fpmul_wg (w k : ℕ) (a b p' : Vector (Exp p (ZMod p)) k) (cont : Vector (ZMod p) k → Wg p) : Wg p :=
  let ab := (toCompPoly (a.map (Exp.eval)))
  range_check_vec_wg w a
    (
      range_check_vec_wg w b
        (
          range_check_vec_wg w p'
          (
            let a_val : ℕ := ∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1
            let b_val : ℕ := ∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1
            let p_val : ℕ := ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1
            let q_val : ℕ := (a_val * b_val) / p
            let r_val : ℕ := (a_val * b_val) % p
            let q_vec := Circuit.nat2words p w k q_val
            let r_vec := Circuit.nat2words p w k r_val
            List.foldr
              (fun i ↦ Wg.cons (ab.coeff i.1))
              (
                q_vec.foldr Wg.cons
                  (range_check_vec_wg w (q_vec.map .v) $
                    r_vec.foldr Wg.cons
                      (
                        range_check_vec_wg w (r_vec.map .v) $
                        -- -(2 ^ (2*n + 1) * k) < - (2^(2*n)*k + 2^n)  < t[i] < (2 ^ (2 * n) * k)
                        let t := ab - (toCompPoly (p'.map (Exp.eval))) * (toCompPoly q_vec) - (toCompPoly r_vec)
                        List.foldr
                          (fun i ↦ Wg.cons (t.coeff i))
                          (
                            check_carry_zero_wg w (Vector.ofFn (fun i : Fin (2 * k - 1) ↦ .v (t.coeff i.1)))
                              (
                                check_lt_wg w (r_vec.map .v) p'
                                (cont r_vec)
                              )
                          )
                          (List.range (2 * k - 1)
                        )
                      )
                  )
              )
              (List.finRange (2 * k - 1))
          )
        )
    )

end Wg

end Clap.FpMul
