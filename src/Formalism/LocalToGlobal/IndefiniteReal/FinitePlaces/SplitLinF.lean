module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLin

@[expose] public section

namespace Formalism.IndefR.Fin

theorem splitLinF (D : Formalism.BasicNotions.D7) : SplitLin D := splitLin_of (placeLatDual D) (latLevelF D)

end Formalism.IndefR.Fin
