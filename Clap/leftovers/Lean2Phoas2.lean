/-

syntactic-only
we can match lists of integer expressions to our syntax w/o semantic equivalance. ?
In this case it's not proof-search, we need to spell out what corresponds to what. e.g. [] to nil | e::cs to eq0 e cs

if we have a close match between wg and lean, can we then replace wg with lean? Over wg we want to do:

-/

def eq0 (e:Int) : (Unit -> Bool) -> Bool :=
  fun k => if e = 0 then k () else False

def share (e:Int) : (Int -> Bool) -> Bool :=
  fun k => k e

def inv (e:Int) : (Int -> Bool) -> Bool :=
  fun k => k ( 1 / e ) -- 1/0 = 0

def is_zero (e:Int) : (Int -> Bool) -> Bool :=
  fun k => k (if e=0 then 0 else 1)

def is_zero_spec (i:Int) : Bool := decide (i=0)

variable (var:Type)
variable (phoas: Type -> Type)

-- evaluating phoas is the same as CPS of spec
def is_zero_phoas (i:Int) : (var -> phoas var) -> phoas var :=
  fun k => k (decide (i=0))

variable (trace: Type)

def is_zero_wg (i:Nat) (t:trace) : trace :=
  fun k => k (decide (i=0))

def is_zero_cs (i o:Int) : List Int :=
  let o := 1 - i * inv ;
  [i*o]

def is_zero_lower : forall i, is_zero i =
