module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0100
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087

@[expose] public section

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof _root_.GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic _root_.GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
