module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsPrincipalPolarisationEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.abelianSchemeLaws_all : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 :=
  _root_.GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one _root_.GlobalTheory.AbLaw.finrank_sections_principal_polarisation_eq_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrincipalPolarisationUniqueSection
section
namespace GlobalTheory.AbLaw

theorem principalPolarisation_unique_section : GlobalTheory.Published.principalPolarisationOneSection :=
  finrank_sections_principal_polarisation_eq_one

end GlobalTheory.AbLaw
end

