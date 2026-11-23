module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProductOfHyps
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RenameMulRenameMemSpanProductBasis
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DominantOfIsHighestWeightVectorPolynomial
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IsotypicSumInfStandardWordsOutsideEqBot
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem externalProduct_basis : ExternalProductBasis := fun R _ N r K LL B => ⟨linearIndependent_productBasis R N r K LL B, span_productBasis_eq_multihomogeneous R N r K LL B⟩

theorem externalProductHyps (D : Formalism.BasicNotions.D7) : ExternalProductHyps := {
  p16 := externalProduct_basis
  e1 := determinant_divisibility
  e2 := polynomialHighestWeight_dominant D
  e3 := projectors_preserve_multidegree
  e5a := polynomialProjectors_commute_nested
  e5b := polynomialProjectors_commute_disjoint
  lowPl := restLowPl_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  lowTan := restLowTan_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  sum := restJointSum }

theorem admissible_externalProduct (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PairedPathIndependence D := admissible_externalProduct_of_hyps D (externalProductHyps D)

end Formalism.MainNotions.G.ColumnFamilies
