module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KAt {k : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH G ∧ g * s = s * g}



end Formalism.IndefR.Tow

end
