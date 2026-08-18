import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Primes

private def scanrAux {α β : Type} (f : α → β → β) (init : β) : List α → β × List β
  | []     => (init, [])
  | a :: l => let (acc, rs) := scanrAux f init l; (f a acc, acc :: rs)

private lemma scanrAux_length {α β : Type} (f : α → β → β) (init : β) (l : List α) :
    (scanrAux f init l).2.length = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [scanrAux, ih]

def Vector.scanr {α β : Type} {n} (f : α → β → β) (init : β) (v : Vector α n) : Vector β n :=
  ⟨⟨(scanrAux f init v.toList).2⟩, by simp [scanrAux_length]⟩

private def scanlAux {α β : Type} (f : β → α → β) (init : β) : List α → List β
  | []     => []
  | a :: l => init :: scanlAux f (f init a) l

private lemma scanlAux_length {α β : Type} (f : β → α → β) (init : β) (l : List α) :
    (scanlAux f init l).length = l.length := by
  induction l generalizing init with
  | nil => rfl
  | cons _ _ ih => simp [scanlAux, ih]

def Vector.scanl {α β : Type} {n} (f : β → α → β) (init : β) (v : Vector α n) : Vector β n :=
  ⟨⟨scanlAux f init v.toList⟩, by simp [scanlAux_length]⟩

namespace Clap

@[reducible]
def typ (a r : Type) : Nat → Type
  | 0     => r
  | n + 1 => a → typ a r n

@[reducible]
def curry {α β : Type} {n : Nat} (k : Vector α n → β) : typ α β n :=
  match n with
  | 0     => k #v[]
  | n + 1 => fun x => curry fun l => k ⟨⟨x :: l.toList⟩, by simp⟩

section

open Lean Meta

/--
This is abstracted over because the current implementation is the simplest approximation
that may (or may not) interfere with the context - if it does, it is easily fixable.

TODO(workaround) Currently a stopgap measure before we incorporate currying in a better way
The better way would involve systematically expressing `v : Vec n` as `#v[v[0], ... v[n-1]]`.
Thus, this will not be needed at all.
-/
def reduceCurry (goal : MVarId) : MetaM MVarId := goal.withContext do
  let ([goal], _) ← Elab.runTactic goal
    (←`(tactic|dsimp -zeta only
      [
        curry, Vector.toList_mk, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ,
        List.getElem_cons_zero
      ]))
    | throwError m!"`reduceCurry` failed in:\n{goal}"
  return goal

elab "reduce_curry" : tactic => Elab.Tactic.liftMetaTactic' reduceCurry

end

/-- Computes minimum number of bits necessary to represent the input. -/
def minBits (x : ℕ) : ℕ :=
  if x = 0 then 1 else
  let nb := Nat.log2 x
  if 2^nb ≤ x then nb + 1 else nb

def minBytes (x : ℕ) : ℕ :=
  let nb := minBits x
  let nb8 := nb / 8
  if nb % 8 = 0 then nb8 else nb8 + 1

def natToHexChar : ℕ → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | 15 => 'f'
  | _ => '*'

def natToBytesBe (n : ℕ) : List ℕ :=
  let q := n / 16
  let r := n % 16
  if q == 0 then [r]
  else natToBytesBe q ++ [r]
decreasing_by grind

def natToHex (n : ℕ) : String :=
  let s := String.ofList ((natToBytesBe n).map natToHexChar)
  if s.length % 2 = 0 then s else "0" ++ s

def natOfBytesBe (a : Array UInt8) : ℕ :=
  (a.reverse.foldl (fun (pow,acc) i => (pow*256, acc + (i.toNat * pow))) (1,0)).2

--#eval natToHex (natOfBytesBe #[0x61, 0x62, 0x63, 0x80])

end Clap

def Lean.Expr.foldlRecM {α : Type}
  {m : Type → Type} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  (f : α → Expr → m α) (init : α) (e : Expr) : m α :=
  (·.2) <$> (
    StateT.run (
      Meta.transform e <| fun e' ↦
        Functor.mapConst TransformStep.continue (get >>= monadLift ∘ flip f e' >>= set)
    ) init
  )

lemma ZMod.val_sum' {m n : ℕ} [NeZero n] {f : Fin m → ZMod n} :
    (∑ i, f i).val =  (∑ i, (f i).val) % n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ZMod.val_add, ih, Nat.add_mod_mod]

lemma ZMod.val_sum {n : ℕ} [NeZero n] {α : Type} [Fintype α] {f : α → ZMod n} :
    (∑ i, f i).val =  (∑ i, (f i).val) % n := by
  rcases Finite.exists_equiv_fin α with ⟨α_size, ⟨exists_bij⟩⟩
  let g := exists_bij.toFun
  let g_inv := exists_bij.invFun
  have h₁ {β : Type} [Semiring β] {f : α → β} : ∑ i, f i = ∑ i, f (g_inv i) := by
    refine Function.Bijective.finsetSum g (Equiv.bijective exists_bij) f (fun x => f (g_inv x)) ?_
    intros x
    congr
    dsimp [g, g_inv]
    exact (Equiv.apply_eq_iff_eq_symm_apply exists_bij).mp rfl
  rw [h₁, h₁]
  exact val_sum'

-- LSB decoding of a bignum limb list into `ℕ`, using base `2^w`
def limbsToNat {p : ℕ} (w : ℕ) : List (ZMod p) → ℕ
    | []      => 0
    | x :: xs => x.val + 2^w * limbsToNat w xs

/- LSB encoding of a `ℕ` into `k` limbs of `w` bits as `ZMod p`. The result always
   has length `k`; higher bits of `n` beyond `k·w` are truncated. -/
def natToLimbs {p : ℕ} (w : ℕ) : ℕ → ℕ → List (ZMod p)
    | 0,     _ => []
    | k + 1, n => ((n % 2^w : ℕ) : ZMod p) :: natToLimbs w k (n / 2^w)

lemma length_natToLimbs {p w k n : ℕ}:
  (natToLimbs (p := p) w k n).length =
  k
:= by
  induction k generalizing n <;> grind [natToLimbs]

def natToLimbsV {p : ℕ} (w : ℕ) (k : ℕ) (n : ℕ) : Vector (ZMod p) k :=
  ⟨⟨natToLimbs w k n⟩, length_natToLimbs⟩

def toChunks {w} {α:Type} (size : ℕ) (bits : Vector α (w*size)) : Vector (Vector α size) w :=
  step 0 (by omega) #v[]
where
  step (cnt:ℕ) (h:cnt<=w) (res : Vector (Vector α size) cnt) : Vector (Vector α size) w :=
    if h : cnt = w
    then
      h ▸ res
    else
      let word : Vector α size :=
        have h : (min ((cnt + 1) * size) (w * size) - cnt * size) = size := by
          grind [Nat.mul_le_mul_right]
        h ▸ bits.extract (cnt*size) ((cnt+1)*size)
      let res := res.push word
      step (cnt+1) (by omega) res
