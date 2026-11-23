module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Bundle0002

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
