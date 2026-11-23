module

public import Development.AutomorphicArithmetic.QuadraticCharacters.LogDerivAtOne

@[expose] public section

open ArithmeticFunction

namespace HostParam

abbrev PrimChar : Type := Σ M : ℕ, DirichletCharacter ℂ M

structure HostType where

namespace HostType

variable (T : HostType)

end HostType

abbrev GalRealCyclotomic (n : ℕ) : Type := (ZMod (4 * n))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * n))ˣ)

end HostParam
