module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0015

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FreeParAlgIndep.full : FreeParAlgIndep.Statement := FreeParAlgIndep.proof

theorem GenSecSeparable.full : GenSecSeparable.Statement :=
  GenSecSeparable.of_freeParAlgIndep FreeParAlgIndep.full

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_freeParAlgIndep FreeParAlgIndep.full

end GroundTheory.Heights₂.Heights.Vertical
