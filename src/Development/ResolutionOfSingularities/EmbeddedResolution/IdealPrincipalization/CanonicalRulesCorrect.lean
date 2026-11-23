module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0008
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometricPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isCorrect_canonicalAlgorithmRules_of_hypotheses
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hdiv : DivisorReduction.DivisorReductionHypotheses hres)
    (hG : PrincipalizationGeometryHypotheses.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  { divisorSpec := isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules hres hdiv
    divisorShift := isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules hres hdiv
    maxOrderSpec := fun n A L hspec =>
      MaxOrderReduction.isMaxOrderReduction_canonicalAlgorithmRules hG hres n A L hspec
    orderSpec := OrderReductionProperties.isOrderReduction_orderFamily_of_strictTransformIsBlowup hres }

theorem isCorrect_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules_of_hypotheses hres
    (divisorReductionHypotheses_canonicalAlgorithmRules hres)
    principalizationGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution
