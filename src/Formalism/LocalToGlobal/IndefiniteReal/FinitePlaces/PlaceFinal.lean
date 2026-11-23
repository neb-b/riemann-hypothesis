module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem placeModelAtF (D : Formalism.BasicNotions.D7) : PlaceModelAt D := placeModelAt_of (placeLatDual D)

theorem latLevelF (D : Formalism.BasicNotions.D7) : LatLevel D := latLevel_of (latSelfDual D)

end Formalism.IndefR.Fin

end
