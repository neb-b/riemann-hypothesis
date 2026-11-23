module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Bundle0001

@[expose] public section

namespace CoverDenseAlt
open GroundTheory.Heights₂.Heights

theorem heightRecR_full : HeightRecR.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM
        (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem chartDehom_full : OrbitChartDehom.Statement :=
  OrbitChartDehom.proof OrbitChartMax.proof OrbitChartQuot.proof

end CoverDenseAlt
