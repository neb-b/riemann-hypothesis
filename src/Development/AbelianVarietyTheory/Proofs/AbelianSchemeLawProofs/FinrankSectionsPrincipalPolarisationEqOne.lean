module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankPrincipalPolarisationSectionModuleLeOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem finrank_sections_principal_polarisation_eq_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1 :=
  fun K _ _ P => le_antisymm (_root_.GlobalTheory.PrincipalSections.finrank_secM_le_one K P) (_root_.GlobalTheory.PolSection.one_le_finrank_secM K P)

end GlobalTheory.AbLaw
