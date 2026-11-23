module

public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

variable (hc : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.MI
