module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0016

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

private theorem coneDim₃ : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ChartPointTrdeg.full : ChartPointTrdeg.Statement :=
  ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
theorem SpecChart.full : SpecChart.Statement := SpecChart.proof
theorem GenericFormsKer.full : GenericFormsKer.Statement := GenericFormsKer.proof
theorem DerivSpanTrdeg.full : DerivSpanTrdeg.Statement := DerivSpanTrdeg.proof

theorem SecPointSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    SecPointSeparable.Statement :=
  SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h

theorem GenSecSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    GenSecSeparable.Statement :=
  GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h)

theorem ChowFormSectionVertical.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full

end GroundTheory.Heights₂.Heights.Vertical
