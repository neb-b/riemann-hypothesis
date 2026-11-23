module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum

namespace UpperTheory.V.B3

section Grp

variable {Γ : Type} [Group Γ]

variable {C : Type} [CommGroup C]

end Grp

section Fld

variable (k L : Type) [Field k] [Field L] [NumberField L] [Algebra k L]

variable (Ω : Type) [Field Ω] [Algebra k Ω]

end Fld

def pPart (m p : ℕ) : Subgroup (ZMod m)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd m p)).ker

end UpperTheory.V.B3

end
