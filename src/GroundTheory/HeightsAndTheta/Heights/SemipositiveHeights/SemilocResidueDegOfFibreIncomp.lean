module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0048

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
