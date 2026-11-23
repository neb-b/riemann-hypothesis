module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalNeZeroOfMemCellMon
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRowLocCoverX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem RowLocCover.closed : RowLocCover.Statement :=
  RowLocCover.proof ChartSecGen.full (ChartSecMul.proof BundleOfDeg.full) RowSub.proof
    RowChartAct.proof

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PZCombLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem ZCombLimit.proof : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof))

end GroundTheory.Heights₂.Heights.Swarm
end

