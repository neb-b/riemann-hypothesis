module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsAlt
section
namespace GlobalTheory.CompanionTheory.DSCapelliAction

theorem actQ : CompanionTheory.D.DSIC.ActQ := by
  intro n ε H _ _ σ S E h u v
  exact GlobalTheory.CapelliFreeAction.actU_qdet n ε H σ S E (fun a b w => h.act a b w) u v

end GlobalTheory.CompanionTheory.DSCapelliAction
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KExp
section
namespace GlobalTheory.CompanionTheory.DSICKExp

theorem kExp : CompanionTheory.D.DSIC.KExp := by
  intro n ε g hg
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.compact_exponential_surjective n ε g hg
  exact ⟨Y, hY, he.symm⟩

end GlobalTheory.CompanionTheory.DSICKExp
end

