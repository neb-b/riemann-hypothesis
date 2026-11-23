module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefBCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.Kleiman

theorem KleimanNefB.segreRealise (hNef : SectionsOverLocalization.NefEq.Statement) (hCh : SectionsOverLocalization.ModelChangeNef.Statement)
    (hNM : SectionsOverLocalization.NumModel.Statement) : SectionsOverLocalization.SegreRealise.Statement :=
  SectionsOverLocalization.SegreRealise.proof SectionsOverLocalization.SegreBase.proof SectionsOverLocalization.SegreTwist.proof SectionsOverLocalization.SegreDim.proof
    (SectionsOverLocalization.SegreNef.proof SectionsOverLocalization.SegreDim.proof SectionsOverLocalization.SegreNum.proof) SectionsOverLocalization.SegreNum.proof
    SectionsOverLocalization.BundleOfDeg.full SectionsOverLocalization.ModelDimEq.full (SectionsOverLocalization.ModelNefEq.proof hNef hCh)
    (SectionsOverLocalization.ModelNumEq.proof hNM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR


open GroundTheory.Heights₂.Heights.FieldNumbers in
theorem DivPushForwardLocalZero : FieldNumbers.DivPushForwardLocal.Statement.{0} := by
  have hq := DegZeroLocQuot.proof.{0}
  have hdzl := DegZeroLocLocal.proof hq
  have hdzn := DegZeroLocNoetherian.proof hq
  have hmh := MChartHomog.proof.{0}
  have hmd := MChartDehomog.proof.{0}
  have hmt := MChartTrdeg.proof hmh
  have hdzr := DegZeroLocalRing.proof hdzl hdzn
    (DegZeroLocDim.proof hmh hmt (MChartLocDim.proof hq hmd hmh))
  have hnum := ConeVarNumerator.proof hq
  have hcone := ConeLocalLength.proof LocalizedQuotientLength.proof
    (ConeLocalFlat.proof (ConePolyLocalization.proof hdzl (ConeVarUnit.proof hq hnum)
      ConeVarSurj.proof (ConeVarInj.proof hnum)))
  have hfr := DegZeroLocFrac.proof.{0}
  have hff := FibreFinite.proof.{0}
  have hint := SemilocalIntegral.proof ValuativeCentre.proof.{0}
  have hrank := SemilocalFiniteRank.proof hff
    (SemilocalFinite.proof hint
      (LocalIntegralClosureFinite.proof NoetherIntegralClosureFinite.proof
        (FunctionFieldFinite.proof hmd hmt) hq hmd hfr) hdzn) hfr
  have hfrd := FibreRelDim.proof.{0}
  have hlz := DegZeroLocLocalize.proof.{0}
  have hres := DegZeroLocResidue.proof.{0}
  have hmaxi := SemilocalMaxIdeals.proof hff hfrd (FibreNonempty.proof hrank hdzr)
    DegZeroLocUnits.proof DegZeroLocSeparate.proof hlz (SemilocalResidueLength.proof hres hrank hlz)
  have hlen := SemilocalLength.proof
    (SemilocalLengthSum.proof hff hrank hdzr FiniteAlgebraLengthSum.proof hmaxi) hfrd
    DivCycleMinimal.proof hcone
  exact DivPushForwardLocal.proof DivCycleMinimal.proof hcone hdzr hrank hlen

theorem FlagBundleDim.full : FlagBundleDim.Statement :=
  FlagBundleDim.proof TwistedDualGensSpan.proof
    (SpanBundleDim.proof PointIdealMultiProj.proof SpanBundleTrdegGe.proof SpanBundleTrdegLe.proof)

theorem NumericalSegre.full : NumericalSegre.Statement :=
  NumericalSegre.of_open FlagBundleDim.full FlagBundleSectionForms.proof
    (FlagBundleSectionDiv.proof FlagBundleDim.full MultAtOfSaturated.proof ProjIdealFormValue.proof
      TruncSpecialize.proof FlagBundleChartSection.proof)
    FlagLineSection.proof FlagLineDegree.proof DivPushForwardLocalZero

end GroundTheory.Heights₂.Heights.NumbersDVR
end

