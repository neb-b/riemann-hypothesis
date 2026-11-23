module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace PositivityTheory.FormalThickening

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation := by
  refine ⟨?_, _root_.GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj _root_.GlobalTheory.CompanionTheory.GE.geClosedProj⟩
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.MorphismAlgebraisation.exists_hom_of_thickenings _root_.GlobalTheory.CompanionTheory.GE.geClosed _root_.GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick R I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact _root_.GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq R I hI X Z hX hZs Y b hb g' g (fun e => (hg' e).trans (hg e).symm)

end PositivityTheory.FormalThickening
