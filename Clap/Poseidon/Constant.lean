import Clap.Primes
import Clap.Poseidon.ConstantC
import Clap.Poseidon.ConstantM
import Clap.Poseidon.ConstantP
import Clap.Poseidon.ConstantS

namespace Clap.Poseidon.Constant

open Primes C M P S

def C : List (List (ZMod bn254)) :=
  [C02, C03, C04, C05, C06, C07, C08, C09, C10, C11, C12, C13, C14, C15, C16, C17]

def M : List (List (List (ZMod bn254))) :=
  [M02, M03, M04, M05, M06, M07, M08, M09, M10, M11, M12, M13, M14, M15, M16, M17]

def P : List (List (List (ZMod bn254))) :=
  [P02, P03, P04, P05, P06, P07, P08, P09, P10, P11, P12, P13, P14, P15, P16, P17]

def S : List (List (ZMod bn254)) :=
  [S02, S03, S04, S05, S06, S07, S08, S09, S10, S11, S12, S13, S14, S15, S16, S17]

end Clap.Poseidon.Constant
