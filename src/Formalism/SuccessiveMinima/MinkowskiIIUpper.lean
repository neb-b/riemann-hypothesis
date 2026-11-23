module

public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.Bundle0002
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.Bundle0001
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
public import Mathlib
public import Formalism.SuccessiveMinima.DefsMink

@[expose] public section

namespace Formalism.FN

theorem minkowskiIIUpper : MinkowskiIIUpper :=
  minkowskiIIUpper_of (minkCore_of partialBoxVolumeMonotoneStep partialBoxVolumeScaling) existsSuccessiveMinimaVectors
    existsAdaptedBasis

end Formalism.FN
