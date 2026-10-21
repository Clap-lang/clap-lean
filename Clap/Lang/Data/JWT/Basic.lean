import Mathlib.Data.Nat.Notation

namespace Clap.Lang

/-- ASCII whitespace at the plain-`ℕ` level, matching `F8.isWhitespace`'s circuit notion. Shared
by every JWT field-parser's `parses` spec, so they all state "this byte is whitespace" against the
same predicate. -/
def isWs (c : ℕ) : Bool := c > 8 && c < 14 || c = 32

end Clap.Lang
