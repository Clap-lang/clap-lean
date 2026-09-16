import Clap.Lang.F8.F8
import Clap.Lang.FB.and
import Clap.Lang.FB.or

namespace Clap.Lang.F8

variable {p : ℕ}

/-- ASCII whitespace: TAB(9), LF(10), VT(11), FF(12), CR(13), or SPACE(32). -/
def isWhitespace [p.AtLeastTwo] (c : F8 p) : ClapM p (FB p) := do
  let eight     ← mkF 8
  let fourteen  ← mkF 14
  let thirtytwo ← mkF 32
  let isLineBreak ← FB.and (← greaterThan c eight) (← lessThan c fourteen)
  let isSpace     ← eq c thirtytwo
  FB.or isLineBreak isSpace

namespace isWhitespace

lemma convertsM [p.AtLeastTwo] {state}
  {e : F8 p}
  {e_val : UInt8}
  (hp : 2^(8+1) < p)
  (h_e : Converts F8.conversion state e e_val)
  :
  ConvertsM FB.conversion
    (isWhitespace e)
    state
    (e_val > 8 && e_val < 14 || e_val = 32)
    True
  := sorry

end isWhitespace

end Clap.Lang.F8
