namespace Levels

abbrev Felt := Int

def inverse : Felt -> Felt := sorry

inductive Exp : Nat -> Type where
  | v : {n:Nat} -> Fin n -> Exp n
  | c : {n:Nat} -> Felt -> Exp n
  | op : {n:Nat} -> Exp n -> Exp n -> Exp n

def lemma_monotonicity {n n':Nat} (h: n ≤ n') (e:Exp n) : Exp n' :=
  open Exp in
  match e with
  | v i => v (Fin.castLE h i)
  | c i => c i
  | op l r => op (lemma_monotonicity h l) (lemma_monotonicity h r)

inductive Cs : Nat -> Nat -> Type where
  | nil : {l:Nat} -> Cs l 0
  | eq0 : {l r:Nat} -> Exp l -> Cs l r -> Cs l r
  | lam : {l r:Nat} -> (r>0) -> Cs (l+1) (r-1) -> Cs l r
-- Use [NeZero] [GT]?

abbrev trace (n:Nat) : Type := Vector Felt n

def eval_e {n:Nat} (e:Exp n) (m:trace n) : Felt :=
  match e with
  | Exp.v v => m.get v
  | Exp.c i => i
  | Exp.op l r => eval_e l m + eval_e r m

def sat {l r:Nat} (cs:Cs l r) (m:trace (l+r)) : Bool :=
  match cs with
  | Cs.nil => True
  | Cs.eq0 e cs =>
    have hm : l = min l (l + r) := by omega
    if eval_e e (hm ▸ (m.take l)) = 0
    then sat cs m
    else False
  | Cs.lam _ cs =>
    have h : l+1+(r-1) = l+r := by omega
    sat cs (h ▸ m)

inductive Wg : Nat -> Nat -> Nat -> Nat -> Type where
  | nil : {l wl:Nat} -> Wg l 0 wl 0
  | eq0 : {l r wl wr:Nat} -> Exp (l+wl) -> Wg l r wl wr -> Wg l r wl wr
  | lam : {l r wl wr:Nat} -> (r>0) -> Wg (l+1) (r-1) wl wr -> Wg l r wl wr
  | share : {l r wl wr:Nat} -> (wr≥1) -> Exp (l+wl) -> Wg l r (wl+1) (wr-1) -> Wg l r wl wr
  | inv : {l r wl wr:Nat} -> (wr≥1) -> Exp (l+wl) -> Wg l r (wl+1) (wr-1) -> Wg l r wl wr
  | isZero : {l r wl wr:Nat} -> (wr≥2) -> Exp (l+wl) -> Wg l r (wl+2) (wr-2) -> Wg l r wl wr

-- example (r:Nat) (h:r>0) : NeZero r := by omega

def gen_trace_aux {l r wl wr:Nat} (wg:Wg l r wl wr) (m:trace r) (w:trace (l+wl)) : Option (trace (l+r+wl+wr)) :=
  match wg with
  | Wg.nil => some w
  | Wg.eq0 e wg =>
    let e := eval_e e w
    if e = 0
    then gen_trace_aux wg m w
    else none
  | Wg.lam p wg' =>
    have hr : NeZero r := by constructor; omega
    have hw : l+1+wl = l+wl+1 := by omega
    have h : l+r+wl+wr = (l+1)+(r-1)+wl+wr := by omega
    let w' := w ++ (Vector.singleton m.head)
    h ▸ gen_trace_aux wg' m.tail (hw ▸ w')
  | Wg.share p e wg' =>
    have h : l+r+wl+wr = l+r+(wl+1)+(wr-1) := by omega
    let e := eval_e e w
    let w' := w ++ (Vector.singleton e)
    h ▸ gen_trace_aux wg' m (w')
  | Wg.inv p e wg' =>
    have h : l+r+wl+wr = l+r+(wl+1)+(wr-1) := by omega
    let e := eval_e e w
    let inv := if e = 0 then 0 else inverse e
    let w' := w ++ (Vector.singleton inv)
    h ▸ gen_trace_aux wg' m (w')
  | Wg.isZero p e wg' =>
    have h : l+r+wl+wr = l+r+(wl+2)+(wr-2) := by omega
    let e := eval_e e w
    let i : Felt := if e = 0 then 0 else 1
    let inv := if e = 0 then 0 else inverse e
    let w' : trace (l+wl+2) := w ++ (Vector.singleton inv) ++ (Vector.singleton i)
    h ▸ gen_trace_aux wg' m (w')

def gen_trace {r wr:Nat} (wg:Wg 0 r 0 wr) (m:trace r) : Option (trace (r+wr)) :=
  let h : r+wr = 0+r+0+wr := by omega
  h ▸ gen_trace_aux wg m (Vector.emptyWithCapacity (r+wr))

-- Optimize

def ex_unopt : Wg 0 2 0 1 :=
  open Exp in
  open Wg in
  lam (by decide)
    (share (by decide)
       (v 0)                   -- x1 = i0
       (lam (by decide)
         (eq0 (op (v 1) (v 2)) -- i2 = x1
            nil)))

def test1 :=
  let m :trace 2 := ⟨#[0,0], by decide⟩
  let m' :trace 3 := ⟨#[0,0,0], by decide⟩
  let a : gen_trace ex_unopt m = some m' := by
    decide
  ()

-- need to fix subtraction
-- def test2 :=
--   let m :trace 2 := ⟨#[0,1], by decide⟩
--   let a : gen_trace ex_unopt m = none := by
--     decide
--   ()


def to_cs {l r wl wr:Nat} (wg:Wg l r wl wr) : Cs (l+wl) (r+wr) :=
  open Exp in
  open Cs in
  match wg with
  | Wg.nil => nil
  | Wg.eq0 e wg => eq0 e (to_cs wg)
  | Wg.lam p wg =>
    have hl : l+1+wl = l+wl+1 := by omega
    have hr : r-1+wr = r+wr-1 := by omega
    have p' : r+wr > 0 := by omega
    let cs : Cs (l+wl+1) (r+wr-1) := hl ▸ hr ▸ to_cs wg
    lam p' cs
  | Wg.share p e wg =>
    let eq : Cs (l+wl+1) (r+wr-1) :=
      have hl : l+(wl+1) = l+wl+1 := by omega
      have hr : r+(wr-1) = r+wr-1 := by omega
      let cs : Cs (l+wl+1) (r+wr-1) := hl ▸ hr▸ to_cs wg
      let i : Fin (l+wl+1) := ⟨l+wl, by omega⟩
      let e : Exp (l+wl+1) := lemma_monotonicity (by omega) e
      eq0 (op (v i) e) cs
    lam (by omega) eq
  | Wg.inv p e wg =>
    let eq : Cs (l+wl+1) (r+wr-1) :=
      have hl : l+(wl+1) = l+wl+1 := by omega
      have hr : r+(wr-1) = r+wr-1 := by omega
      let cs : Cs (l+wl+1) (r+wr-1) := hl ▸ hr▸ to_cs wg
      let i : Fin (l+wl+1) := ⟨l+wl, by omega⟩
      let e : Exp (l+wl+1) := lemma_monotonicity (by omega) e
      eq0 (op (v i) e) cs
    lam (by omega) eq
  | Wg.isZero p e wg =>
    let eq : Cs (l+wl+2) (r+wr-2) :=
      have hl : l+(wl+2) = l+wl+2 := by omega
      have hr : r+(wr-2) = r+wr-2 := by omega
      let cs : Cs (l+wl+2) (r+wr-2) := hl ▸ hr▸ to_cs wg
      let inv : Fin (l+wl+2) := ⟨l+wl, by omega⟩
      let i : Fin (l+wl+2) := ⟨l+wl+1, by omega⟩
      let e : Exp (l+wl+2) := lemma_monotonicity (by omega) e
      eq0 (op (v inv) (op (v i) e)) cs
    lam (by omega) (lam (by omega) eq)

def get_inputs_aux {l r wl wr:Nat} (wg:Wg l r wl wr) (m:trace (r+wr)) (ins:trace l) : trace (l+r) :=
  match wg with
  | Wg.nil => ins
  | Wg.eq0 _ wg => get_inputs_aux wg m ins
  | Wg.lam p wg =>
    have hm : r-1+wr = r+wr-1 := by omega
    have h : l + 1 + (r - 1) = l + r := by omega
    have : NeZero (r+wr) := by constructor; omega
    let ins := ins ++ Vector.singleton m.head
    h ▸ get_inputs_aux wg (hm ▸ m.tail) ins
  | Wg.share p e wg
  | Wg.inv p e wg =>
    have hm : r+wr-1 = r+(wr-1) := by omega
    get_inputs_aux wg (hm ▸ m.tail) ins
  | Wg.isZero p e wg =>
    have hm : r+wr-1-1 = r+(wr-2) := by omega
    get_inputs_aux wg (hm ▸m.tail.tail) ins

def get_inputs {r wr:Nat} (wg:Wg 0 r 0 wr) (m:trace (r+wr)) : trace r :=
  have h: 0+r = r := by omega
  h ▸ get_inputs_aux wg m (Vector.emptyWithCapacity r)

def soundness {r wr:Nat} (wg:Wg 0 r 0 wr) : Prop :=
  have hm : r+wr = 0+0+(r+wr) := by omega
  ∀ m, sat (to_cs wg) m →
    Option.isSome (gen_trace wg (get_inputs wg (hm ▸ m)))

def completeness {r wr:Nat} (wg:Wg 0 r 0 wr) : Prop :=
  have hm : r+wr = 0+0+(r+wr) := by omega
  ∀ m m', gen_trace wg m = some m' → sat (to_cs wg) (hm ▸ m')

end Levels
