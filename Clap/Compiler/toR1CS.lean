import Clap.Model.ConstraintSystem.toCs
import Clap.Compiler.Serialize

/-!
# R1CS reduction

`quadraticToR1CS` lowers every zero assertion of a `ConstraintSystem` into exactly one R1CS row
`A * B = C`. It never adds witness variables: the wires are ONE followed by the `numVars`
original trace slots, so the R1CS witness is `[1] ++ trace`.
-/

namespace Clap.ConstraintSystem

open Clap.Serialize

variable {p : Nat} [Fact (Nat.Prime p)]

/-- A binary node that is not rank-1 unless one of its operands becomes a witness variable.
For `.mul`, every listed operand must be shared. For `.add` and `.sub`, sharing either one is
enough. -/
structure ShareSite where
  /-- index in `ConstraintSystem.eq0s` of the assertion where `node` was first reached -/
  assertion : Nat
  /-- the offending `*`, `+` or `-` node -/
  node : ExprRef
  op : BinaryOp
  /-- its quadratic operands, without duplicates -/
  operands : Array ExprRef
  deriving Repr, BEq

inductive CompileError where
  | invalidRoot (ref : Nat)
  | invalidVariable (idx : Nat)
  | invalidInputCount
  | sizeOverflow
  | witnessLength
  /-- the system needs `share` gates at these sites -/
  | needsShare (sites : Array ShareSite)
  deriving Repr, BEq

/-- Sorted coefficients using wire indices (zero is the constant wire).
`[(0, 3), (1, 2), (2, 5)]` represents `3 + 2*x + 5*y` -/
abbrev Coefficients (p : Nat) := List (Nat × ZMod p)

def insertCoeff (i : Nat) (v : ZMod p) : Coefficients p → Coefficients p
  | [] => if v == 0 then [] else [(i,v)]
  | (j,w)::xs =>
    if i < j then (if v == 0 then (j,w)::xs else (i,v) :: (j,w) :: xs)
    else if i == j then (if v + w == 0 then xs else (j, v + w) :: xs)
    else (j, w) :: insertCoeff i v xs

/-- `a + b`, inserting the terms of `b` into `a` one by one -/
def addCoeffsInto (a b : Coefficients p) : Coefficients p := b.foldl (fun a (i,v) ↦ insertCoeff i v a) a

/-- `a + b`. The shorter list is inserted into the longer one -/
def addCoeffs (a b : Coefficients p) : Coefficients p :=
  if b.length ≤ a.length then addCoeffsInto a b else addCoeffsInto b a

/-- `k * a` -/
def scaleCoeffs (k : ZMod p) (a : Coefficients p) : Coefficients p := (a.map fun (i,v) ↦ (i,k * v)).filter (fun x ↦ x.2 ≠ 0)

/-- `a - b = a + (-1) * b` -/
def subCoeffs (a b : Coefficients p) : Coefficients p := addCoeffs a (scaleCoeffs (-1) b)

def constantCoeffs (k : ZMod p) : Coefficients p := insertCoeff 0 k []

def variableCoeffs (i : Nat) : Coefficients p := [(i + 1, 1)]

def evalCoeffs (ρ : Nat → ZMod p) : Coefficients p → ZMod p
  | [] => 0
  | (i, v) :: xs => v * ρ i + evalCoeffs ρ xs

theorem eval_insertCoeff (ρ : Nat → ZMod p) (i : Nat) (v : ZMod p) (a : Coefficients p) :
    evalCoeffs ρ (insertCoeff i v a) = v * ρ i + evalCoeffs ρ a := by
  induction a with
  | nil =>
    simp only [insertCoeff]
    split <;> simp_all [evalCoeffs]
  | cons x xs ih =>
    rcases x with ⟨j,w⟩
    simp only [insertCoeff]
    split
    · split <;> simp_all [evalCoeffs, add_left_comm]
    · split
      · rename_i h
        have : i = j := by simpa using h
        subst j
        split
        · simp only [evalCoeffs]
          rename_i hv
          have hv' : v + w = 0 := by simpa using hv
          have hz := congrArg (fun t : ZMod p => t * ρ i) hv'
          simp only [add_mul, zero_mul] at hz
          linear_combination -hz
        · simp [evalCoeffs, add_mul, add_assoc]
      · simp only [evalCoeffs, ih]
        ring

theorem eval_addCoeffsInto (ρ : Nat → ZMod p) (a b : Coefficients p) :
    evalCoeffs ρ (addCoeffsInto a b) = evalCoeffs ρ a + evalCoeffs ρ b := by
  unfold addCoeffsInto
  induction b generalizing a with
  | nil => simp [evalCoeffs]
  | cons x xs ih =>
    rcases x with ⟨i,v⟩
    simp only [List.foldl_cons, ih, eval_insertCoeff, evalCoeffs]
    ring

theorem eval_addCoeffs (ρ : Nat → ZMod p) (a b : Coefficients p) :
    evalCoeffs ρ (addCoeffs a b) = evalCoeffs ρ a + evalCoeffs ρ b := by
  unfold addCoeffs
  split <;> simp only [eval_addCoeffsInto, add_comm]

theorem eval_scaleCoeffs (ρ : Nat → ZMod p) (k : ZMod p) (a : Coefficients p) :
    evalCoeffs ρ (scaleCoeffs k a) = k * evalCoeffs ρ a := by
  induction a with
  | nil => simp [scaleCoeffs, evalCoeffs]
  | cons x xs ih =>
    rcases x with ⟨i,v⟩
    simp only [scaleCoeffs, List.map_cons, List.filter_cons]
    split
    · simp_all [evalCoeffs, scaleCoeffs, mul_add, mul_assoc]
    · rename_i h
      by_cases hk : k = 0
      · simp_all [evalCoeffs, scaleCoeffs]
      · have hv : v = 0 := by simpa [hk] using h
        simp_all [evalCoeffs, scaleCoeffs]

theorem eval_subCoeffs (ρ : Nat → ZMod p) (a b : Coefficients p) :
    evalCoeffs ρ (subCoeffs a b) = evalCoeffs ρ a - evalCoeffs ρ b := by
  simp [subCoeffs, eval_addCoeffs, eval_scaleCoeffs, sub_eq_add_neg]

/-! The iden3 r1cs format requires the terms of a linear combination sorted by wire id ("The factors
MUST be sorted in ascending order") -/

/-- Strictly increasing wire ids. -/
def SortedCoeffs (a : Coefficients p) : Prop := a.Pairwise (fun x y ↦ x.1 < y.1)

theorem fst_mem_insertCoeff {i : Nat} {v : ZMod p} {x : Nat × ZMod p} :
    ∀ {a : Coefficients p}, x ∈ insertCoeff i v a → x.1 = i ∨ ∃ y ∈ a, y.1 = x.1
  | [], h => by
    simp only [insertCoeff] at h
    split at h <;> simp_all
  | (j, w) :: ys, h => by
    simp only [insertCoeff] at h
    split at h
    · split at h
      · exact .inr ⟨x, h, rfl⟩
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inl rfl
        · exact .inr ⟨x, by simpa using h, rfl⟩
    · split at h
      · rename_i hij
        have hij : i = j := by simpa using hij
        split at h
        · exact .inr ⟨x, List.mem_cons_of_mem _ h, rfl⟩
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact .inr ⟨(j, w), List.mem_cons_self, rfl⟩
          · exact .inr ⟨x, List.mem_cons_of_mem _ h, rfl⟩
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inr ⟨(j, w), List.mem_cons_self, rfl⟩
        · rcases fst_mem_insertCoeff h with h' | ⟨y, hy, h'⟩
          · exact .inl h'
          · exact .inr ⟨y, List.mem_cons_of_mem _ hy, h'⟩

theorem sortedCoeffs_insertCoeff (i : Nat) (v : ZMod p) :
    ∀ {a : Coefficients p}, SortedCoeffs a → SortedCoeffs (insertCoeff i v a)
  | [], _ => by
    simp only [insertCoeff]
    split <;> simp [SortedCoeffs]
  | (j, w) :: ys, h => by
    have hys : SortedCoeffs ys := (List.pairwise_cons.mp h).2
    have hj : ∀ z ∈ ys, j < z.1 := (List.pairwise_cons.mp h).1
    simp only [insertCoeff]
    split
    · rename_i hij
      split
      · exact h
      · refine List.Pairwise.cons ?_ h
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hij
        · exact lt_trans hij (hj z hz)
    · split
      · rename_i hij
        have hij : i = j := by simpa using hij
        split
        · exact hys
        · exact List.Pairwise.cons (by simpa [hij] using hj) hys
      · rename_i hlt hne
        have hji : j < i := by
          have : i ≠ j := by simpa using hne
          omega
        refine List.Pairwise.cons ?_ (sortedCoeffs_insertCoeff i v hys)
        intro z hz
        rcases fst_mem_insertCoeff hz with h' | ⟨y, hy, h'⟩
        · rw [h']; exact hji
        · rw [← h']; exact hj y hy

theorem sortedCoeffs_addCoeffsInto {a b : Coefficients p} (ha : SortedCoeffs a) :
    SortedCoeffs (addCoeffsInto a b) := by
  unfold addCoeffsInto
  induction b generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih (sortedCoeffs_insertCoeff _ _ ha)

theorem sortedCoeffs_scaleCoeffs (k : ZMod p) {a : Coefficients p} (ha : SortedCoeffs a) :
    SortedCoeffs (scaleCoeffs k a) := by
  unfold scaleCoeffs SortedCoeffs
  refine List.Pairwise.sublist List.filter_sublist (List.pairwise_map.mpr ?_)
  exact ha.imp fun {x y} h ↦ by rcases x with ⟨i, v⟩; rcases y with ⟨j, w⟩; exact h

theorem sortedCoeffs_constantCoeffs (k : ZMod p) : SortedCoeffs (constantCoeffs k) :=
  sortedCoeffs_insertCoeff _ _ (by simp [SortedCoeffs])

theorem sortedCoeffs_variableCoeffs (i : Nat) : SortedCoeffs (p := p) (variableCoeffs i) := by
  simp [SortedCoeffs, variableCoeffs]

/-- `a.length ≤ b.length`, walking only as far as the shorter list. -/
def shorterOrEq {α β : Type} : List α → List β → Bool
  | [], _ => true
  | _ :: _, [] => false
  | _ :: xs, _ :: ys => shorterOrEq xs ys

theorem shorterOrEq_eq {α β : Type} (a : List α) (b : List β) :
    shorterOrEq a b = decide (a.length ≤ b.length) := by
  induction a generalizing b with
  | nil => simp [shorterOrEq]
  | cons x xs ih => cases b <;> simp [shorterOrEq, ih]

/-- `k • terms` when `factor = some (k, k⁻¹)`, and `terms` when `factor = none`. -/
structure ScaledCoeffs (p : Nat) where
  factor : Option (ZMod p × ZMod p)
  terms : Coefficients p

namespace ScaledCoeffs

def ofCoeffs (a : Coefficients p) : ScaledCoeffs p := ⟨none, a⟩

/-- The coefficients, with the factor multiplied out. -/
def toCoeffs (s : ScaledCoeffs p) : Coefficients p :=
  match s.factor with
  | none => s.terms
  | some (k, _) => scaleCoeffs k s.terms

/-- `k • s`, where `kinv = k⁻¹` when `k ≠ 0`. -/
def smul (k kinv : ZMod p) (s : ScaledCoeffs p) : ScaledCoeffs p :=
  if k == 0 then ofCoeffs [] else
  match s.factor with
  | none => ⟨some (k, kinv), s.terms⟩
  | some (a, ainv) => ⟨some (k * a, ainv * kinv), s.terms⟩

/-- `-s` -/
def neg (s : ScaledCoeffs p) : ScaledCoeffs p := smul (-1) (-1) s

/-- `small`'s terms relative to `big`'s factor. `big⁻¹ • small` without `big`'s factor. -/
def relativeTerms (big small : ScaledCoeffs p) : Coefficients p :=
  match big.factor, small.factor with
  | none, none => small.terms
  | none, some (k, _) => scaleCoeffs k small.terms
  | some (_, binv), none => scaleCoeffs binv small.terms
  | some (_, binv), some (k, _) => scaleCoeffs (binv * k) small.terms

/-- `big + small`, inserting `small`'s terms into `big`'s, the sum keeps `big`'s factor. -/
def addInto (big small : ScaledCoeffs p) : ScaledCoeffs p :=
  if small.terms.isEmpty then big else ⟨big.factor, addCoeffsInto big.terms (relativeTerms big small)⟩

/-- `a + b`, inserting the shorter list into the longer one, as `addCoeffs` does. -/
def add (a b : ScaledCoeffs p) : ScaledCoeffs p :=
  if shorterOrEq b.terms a.terms then addInto a b else addInto b a

/-- `a - b` -/
def sub (a b : ScaledCoeffs p) : ScaledCoeffs p := add a (neg b)

/-- `constantValue? s.toCoeffs`, without multiplying out. -/
def constantValue? (s : ScaledCoeffs p) : Option (ZMod p) :=
  match s.terms, s.factor with
  | [], _ => some 0
  | [(0, v)], none => some v
  | [(0, v)], some (k, _) => some (k * v)
  | _, _ => none

/-- The same form without a factor, or `none` when it has none. -/
def normalized? (s : ScaledCoeffs p) : Option (ScaledCoeffs p) :=
  s.factor.map fun _ ↦ ofCoeffs s.toCoeffs

end ScaledCoeffs

/-- `A * B - C` -/
structure NormalQuadratic (p : Nat) where
  A : Coefficients p
  B : Coefficients p
  C : Coefficients p

/-- `A * B - C` with scaled sides. -/
structure ScaledQuadratic (p : Nat) where
  A : ScaledCoeffs p
  B : ScaledCoeffs p
  C : ScaledCoeffs p

/-- A lowered node: linear, or one product minus a linear form. -/
abbrev Form (p : Nat) := ScaledCoeffs p ⊕ ScaledQuadratic p

/-- The form with its factors multiplied out. -/
def Form.toNormal : Form p → Coefficients p ⊕ NormalQuadratic p
  | .inl a => .inl a.toCoeffs
  | .inr q => .inr ⟨q.A.toCoeffs, q.B.toCoeffs, q.C.toCoeffs⟩

/-- The same form without factors, or `none` when it has none. -/
def Form.normalized? : Form p → Option (Form p)
  | .inl a => a.normalized?.map .inl
  | .inr q =>
    if q.A.factor.isNone && q.B.factor.isNone && q.C.factor.isNone then none
    else some (.inr ⟨q.A.normalized?.getD q.A, q.B.normalized?.getD q.B, q.C.normalized?.getD q.C⟩)

structure QuadraticSt (p : Nat) where
  memo : Std.HashMap Nat (Form p) := {}
  /-- operands already reported in a share site, each mapped to a placeholder variable index
  `≥ numVars`. Lowering continues as if they were shared, so one run reports every site. -/
  assumed : Std.HashMap Nat Nat := {}
  sites : Array ShareSite := #[]
  rows : Array (NormalQuadratic p) := #[]
  /-- `k⁻¹` for each nonzero constant factor `k` met so far, by `k.val` -/
  inverses : Std.HashMap Nat (ZMod p) := {}

abbrev QuadraticM (p : Nat) := StateT (QuadraticSt p) (Except CompileError)

/-- `k⁻¹` (for `k ≠ 0`), computed once per constant. -/
def inverseOf (k : ZMod p) : QuadraticM p (ZMod p) := do
  if let some v := (← get).inverses[k.val]? then return v
  let v := ZMod.inv p k
  modify fun s ↦ { s with inverses := s.inverses.insert k.val v }
  return v

def assumeShared (numVars ref : Nat) (x : Form p) : QuadraticM p (ScaledCoeffs p) := do
  match x with
  | .inl a => return a
  | .inr _ =>
    let s ← get
    if let some idx := s.assumed[ref]? then return .ofCoeffs (variableCoeffs idx)
    let idx := numVars + s.assumed.size
    set { s with assumed := s.assumed.insert ref idx }
    return .ofCoeffs (variableCoeffs idx)

def reportSite (assertion node : Nat) (op : BinaryOp) (operands : Array Nat) : QuadraticM p Unit := do
  unless operands.isEmpty do
    modify fun s ↦ { s with sites := s.sites.push ⟨assertion, node, op, operands⟩ }

/-- For `x ± y` with two quadratic operands, decide which one stands for a shared variable.
An operand that is already assumed shared costs nothing (the right one first). Otherwise report
the node -/
def shareLeft (assertion node lr rr : Nat) (op : BinaryOp) : QuadraticM p Bool := do
  let s ← get
  if s.assumed.contains rr then return false
  if s.assumed.contains lr then return true
  reportSite assertion node op (if lr == rr then #[rr] else #[rr, lr])
  return false

def addQuadratic (numVars assertion node lr rr : Nat) (x y : Form p) : QuadraticM p (Form p) := do
  match x, y with
  -- a + b
  | .inl a, .inl b => return .inl (a.add b)
  -- (a * b - c) + l = a * b - (c - l)
  | .inr ⟨a, b, c⟩, .inl l | .inl l, .inr ⟨a, b, c⟩ => return .inr ⟨a, b, c.sub l⟩
  | x@(.inr ⟨a, b, c⟩), y@(.inr ⟨a', b', c'⟩) =>
    if ← shareLeft assertion node lr rr .add then
      let l ← assumeShared numVars lr x
      -- l + (a' * b' - c') = a' * b' - (c' - l)
      return .inr ⟨a', b', c'.sub l⟩
    else
      let l ← assumeShared numVars rr y
      -- (a * b - c) + l = a * b - (c - l)
      return .inr ⟨a, b, c.sub l⟩

def subQuadratic (numVars assertion node lr rr : Nat) (x y : Form p) : QuadraticM p (Form p) := do
  match x, y with
  -- a - b
  | .inl a, .inl b => return .inl (a.sub b)
  -- (a * b - c) - l = a * b - (c + l)
  | .inr ⟨a, b, c⟩, .inl l => return .inr ⟨a, b, c.add l⟩
  -- l - (a * b - c) = (-a) * b - (-(c + l))
  | .inl l, .inr ⟨a, b, c⟩ => return .inr ⟨a.neg, b, (c.add l).neg⟩
  | x@(.inr ⟨a, b, c⟩), y@(.inr ⟨a', b', c'⟩) =>
    if ← shareLeft assertion node lr rr .sub then -- as in the `.inl l, .inr _` case, `l` shared
      let l ← assumeShared numVars lr x
      -- l - (a' * b' - c') = (-a') * b' - (-(c' + l))
      return .inr ⟨a'.neg, b', (c'.add l).neg⟩
    else
      let l ← assumeShared numVars rr y
      -- (a * b - c) - l = a * b - (c + l)
      return .inr ⟨a, b, c.add l⟩

def mulByConstant (k : ZMod p) (x : Form p) : QuadraticM p (Form p) := do
  -- 0 * a = 0, and 0 * (a * b - c) = 0
  if k == 0 then return .inl (.ofCoeffs [])
  let kinv ← inverseOf k
  match x with
  -- k * a
  | .inl a => return .inl (a.smul k kinv)
  -- k * (a * b - c) = (k * a) * b - k * c
  | .inr ⟨a, b, c⟩ => return .inr ⟨a.smul k kinv, b, c.smul k kinv⟩

/-- A product is rank-1 only when both factors are linear (or one is constant). Quadratic factors
that are not already assumed shared make one share site. -/
def mulQuadratic (numVars assertion node lr rr : Nat) (x y : Form p) : QuadraticM p (Form p) := do
  if let .inl a := x then
    if let some k := a.constantValue? then
      return ← mulByConstant k y
  if let .inl b := y then
    if let some k := b.constantValue? then
      return ← mulByConstant k x
  let s ← get
  let pending (ref : Nat) (f : Form p) := f.isRight && !s.assumed.contains ref
  reportSite assertion node .mul <| (if pending lr x then #[lr] else #[]) ++ (if pending rr y && rr != lr then #[rr] else #[])
  let a ← assumeShared numVars lr x
  let b ← assumeShared numVars rr y
  return .inr ⟨a, b, .ofCoeffs []⟩

inductive QuadraticFrame where
  | visit (ref : Nat) -- "lower this node, unless it is already done"
  | finish (ref l r : Nat) (op : BinaryOp) -- "both children are done; combine them"

-- The weights are used only in the termination proof, not by the traversal.
def frameWeight : QuadraticFrame → Nat
  | .visit ref => 3 ^ (ref + 1)
  | .finish _ _ _ _ => 1

def framesWeight : List QuadraticFrame → Nat
  | [] => 0
  | f :: fs => frameWeight f + framesWeight fs

theorem visit_expands (ref l r : Nat) (hl : l < ref) (hr : r < ref) :
    3 ^ (l + 1) + (3 ^ (r + 1) + 1) < 3 ^ (ref + 1) := by
  have hl' : 3 ^ (l + 1) ≤ 3 ^ ref := Nat.pow_le_pow_right (by omega) (by omega)
  have hr' : 3 ^ (r + 1) ≤ 3 ^ ref := Nat.pow_le_pow_right (by omega) (by omega)
  have hp : 0 < 3 ^ ref := Nat.pow_pos (by omega)
  rw [pow_succ]
  omega

/-- Lowers expressions in left-to-right depth-first order. -/
def normalQuadraticLoop (σ : HashConsSt p) (numVars assertion : Nat) (frames : List QuadraticFrame) : QuadraticM p Unit := do
  match frames with
  | [] => pure ()
  | .visit ref :: rest =>
    if let some form := (← get).memo[ref]? then
      if let some form := form.normalized? then
        modify fun s ↦ { s with memo := s.memo.insert ref form }
      normalQuadraticLoop σ numVars assertion rest
    else
      match _ : σ[ref]? with
      | none => throw (.invalidRoot ref)
      | some (.c k) =>
        modify fun s ↦ { s with memo := s.memo.insert ref (.inl (.ofCoeffs (constantCoeffs k))) }
        normalQuadraticLoop σ numVars assertion rest
      | some (.v i) =>
        if i < numVars then
          modify fun s ↦ { s with memo := s.memo.insert ref (.inl (.ofCoeffs (variableCoeffs i))) }
          normalQuadraticLoop σ numVars assertion rest
        else throw (.invalidVariable i)
      | some (.binary_op l r op) =>
        normalQuadraticLoop σ numVars assertion (.visit l :: .visit r :: .finish ref l r op :: rest)
  | .finish ref l r op :: rest =>
    let s ← get
    match s.memo[l]?, s.memo[r]? with
    | some a, some b =>
      let result ← match op with
        | .add => addQuadratic numVars assertion ref l r a b
        | .sub => subQuadratic numVars assertion ref l r a b
        | .mul => mulQuadratic numVars assertion ref l r a b
      modify fun s ↦ { s with memo := s.memo.insert ref result }
      normalQuadraticLoop σ numVars assertion rest
    -- Both child visits precede this frame and successful visits populate the memo.
    | _, _ => throw (.invalidRoot ref)
termination_by framesWeight frames
decreasing_by
  all_goals simp only [framesWeight, frameWeight]
  all_goals try { exact Nat.lt_add_of_pos_left (Nat.pow_pos (by decide)) }
  all_goals try omega
  have h_lt : ref < σ.exprs.size := by
    by_contra h_ge
    simp_all
  have hw := σ.wellFormed ref h_lt
  have hw' : l < ref ∧ r < ref := by simp_all [CacheExpr.wellFormed]
  have := visit_expands ref l r hw'.1 hw'.2
  omega

/-- lowers one source expression into quadratic form -/
def normalQuadratic₀ (σ : HashConsSt p) (numVars assertion ref : Nat) : QuadraticM p (Coefficients p ⊕ NormalQuadratic p) := do
  normalQuadraticLoop σ numVars assertion [.visit ref]
  match (← get).memo[ref]? with
  | some result => return result.toNormal
  | none => throw (.invalidRoot ref) -- successful traversal populates the root

/- linear: L → L * 1 = 0; quadratic: A * B - C → A * B = C -/
def normalQuadratic (numVars : Nat) (σ : HashConsSt p) (assertion ref : Nat) : QuadraticM p Unit := do
  let x ← normalQuadratic₀ σ numVars assertion ref
  let row := match x with
    | .inl a => NormalQuadratic.mk a (constantCoeffs 1) []
    | .inr q => q
  modify fun s => { s with rows := s.rows.push row }

def checked32 (n : Nat) : Except CompileError UInt32 :=
  if n < UInt32.size then .ok (UInt32.ofNat n) else .error .sizeOverflow

def checked64 (n : Nat) : Except CompileError UInt64 :=
  if n < UInt64.size then .ok (UInt64.ofNat n) else .error .sizeOverflow

/-- The byte size of the serialized constraints section payload: `Constraint.byteSize` summed over
the rows, as `R1CSv1.constraintsByteSize` counts it. -/
def constraintBytes (fieldSize : Nat) (rows : Array Constraint) : Nat :=
  rows.foldl (fun size row ↦ size + row.byteSize fieldSize) 0

def coefficientsToTerms (a : Coefficients p) : Except CompileError (Array (UInt32 × Nat)) := do
  a.toArray.mapM fun (i,v) ↦ do return (← checked32 i, v.val)

def quadraticToConstraint (r : NormalQuadratic p) : Except CompileError Constraint := do
  let a ← coefficientsToTerms r.A
  let b ← coefficientsToTerms r.B
  let c ← coefficientsToTerms r.C
  return ⟨← checked32 a.size, ← checked32 b.size, ← checked32 c.size, a,b,c⟩

/-- Lower assertions `i, i+1, …` in order, one row each (tail recursive loop) -/
def lowerAssertions (σ : HashConsSt p) (numVars : Nat) (eq0s : Array ExprRef) (i : Nat)
    (st : QuadraticSt p) : Except CompileError (QuadraticSt p) :=
  if h : i < eq0s.size then
    match (normalQuadratic numVars σ i eq0s[i]).run st with
    | .ok ((), st) => lowerAssertions σ numVars eq0s (i + 1) st
    | .error e => .error e
  else .ok st
termination_by eq0s.size - i

def rowsToConstraints (rows : Array (NormalQuadratic p)) (i : Nat) (acc : Array Constraint) :
    Except CompileError (Array Constraint) :=
  if h : i < rows.size then
    match quadraticToConstraint rows[i] with
    | .ok c => rowsToConstraints rows (i + 1) (acc.push c)
    | .error e => .error e
  else .ok acc
termination_by rows.size - i

structure Compilation (p : Nat) where
  -- the resulting R1CSv1: constraints, header, and wire-to-label map.
  r1cs : R1CSv1
  -- number of witness slots, the wires are ONE followed by these slots.
  numVars : Nat

/-- Compile all assertions, one R1CS row each. Throws `needsShare` with every share site when
some reachable node is not rank-1; the compiler never adds witness variables.

The first `numPublic` trace slots are the public inputs and the next `numPrivate` the private
ones, so the wires are `[ONE, public…, private…, internal…]`: the order the r1cs format and
snarkjs expect, with no public outputs. -/
def quadraticToR1CS (cs : ConstraintSystem p) (numPublic numPrivate numVars : Nat) :
    Except CompileError (Compilation p) := do
  if numPublic + numPrivate > numVars then throw .invalidInputCount
  let wires := numVars + 1
  let nWires ← checked32 wires
  let st ← lowerAssertions cs.σ numVars cs.eq0s 0 {}
  unless st.sites.isEmpty do throw (.needsShare st.sites)
  let nPublic ← checked32 numPublic
  let nPrivate ← checked32 numPrivate
  let nRows ← checked32 st.rows.size
  -- the least multiple of 8 bytes that holds every residue mod p
  let fieldSize ← checked32 (Serialize.fieldSizeFor p)
  let rows ← rowsToConstraints st.rows 0 (.emptyWithCapacity st.rows.size)
  let _ ← checked64 (constraintBytes fieldSize.toNat rows)
  let labels := Serialize.arrayOfFn wires UInt64.ofNat
  let header : Header := ⟨fieldSize, p, nWires, 0, nPublic, nPrivate, UInt64.ofNat wires, nRows⟩
  let r1cs : R1CSv1 := ⟨header, rows, labels, (), ()⟩
  return ⟨r1cs, numVars⟩

/-- The R1CS of `cs`, or why it has none. -/
def toR1CS (cs : ConstraintSystem p) (numPublic numPrivate numVars : Nat) :
    Except CompileError R1CSv1 :=
  (quadraticToR1CS cs numPublic numPrivate numVars).map (·.r1cs)

/-- The R1CS witness is the trace behind the ONE wire. -/
def Compilation.toWtns (compiled : Compilation p) (slots : Array (ZMod p)) : Except CompileError Witness := do
  if slots.size != compiled.numVars then throw .witnessLength
  let values := Serialize.arrayOfFn (slots.size + 1) fun i ↦
    if i = 0 then 1 else (slots[i - 1]?.map ZMod.val).getD 0
  return ⟨compiled.r1cs.header.fieldElemSize, p, compiled.r1cs.header.nWires, values⟩

end Clap.ConstraintSystem
