import Clap.Lang.F.lessThan
import Clap.Lang.FB.eq

namespace Clap.Lang.F8

variable {p : ℕ}

def eq [p.AtLeastTwo] (a b : F p) : ClapM p (FB p) := Clap.Lang.eq a b

def lessThan (a b : F p) : ClapM p (FB p) := Clap.Lang.lessThan 8 a b

def greaterThan (a b : F p) : ClapM p (FB p) := Clap.Lang.greaterThan 8 a b

end Clap.Lang.F8
