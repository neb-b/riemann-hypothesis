module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSumOfParts
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
public import Mathlib
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0001

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies.Top
