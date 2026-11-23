module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TV

namespace Formalism.MainNotions.V

variable {D : D7} (V : VData D)

def scalarGL (R : Type) [CommRing R] (n : ℕ) : Rˣ →* GL (Fin n) R :=
  Units.map (Matrix.scalar (Fin n) : R →+* Matrix (Fin n) (Fin n) R).toMonoidHom

def charRep {H R : Type} [Group H] [CommRing R] (χ : H →* Rˣ) : H →* GL (Fin 1) R :=
  (scalarGL R 1).comp χ


variable {V}

end Formalism.MainNotions.V
