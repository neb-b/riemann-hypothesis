module

public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0003
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0005
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0004
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0002
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0006

@[expose] public section

noncomputable section

namespace Formalism.ZF

theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

theorem zeroFreeRegion : ZeroFreeRegion :=
  classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    zeroFreeBoundedHeight landauLocal

end Formalism.ZF
