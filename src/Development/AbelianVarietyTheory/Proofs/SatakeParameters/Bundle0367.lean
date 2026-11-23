module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsProjOverSPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem isProjOver_sPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N →
    N.Coprime p → ∀ (X : GenModel gb N) (r : ℕ), IsProjOver (sPow X r) := by
  intro p _ D hC gb N hN hNp X r
  have hX : IsProjOver X.s := GlobalTheory.UPel.HT.GenProj.isProjOver_genModel p D hC gb N hN hNp X
  exact GlobalTheory.KS.isProjOver_pow ℂ X.X X.s hX X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample r

end GlobalTheory.WeightTwoHeckePower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem sPow_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ (X : GenModel gb N) (r : ℕ),
    ∃ d : ℕ, SmoothOfRelativeDimension d (sPow X r) := by
  intro G gb N hN X r
  obtain ⟨⟨d, hd⟩, hA⟩ := GlobalTheory.UPel.HT.Gen.CxSmooth.genModel_smooth G gb N hN X
  have h := GlobalTheory.FibPow.smoothOfRelativeDimension_pow X.univ.A _ hA r
  exact ⟨_, (inferInstance : SmoothOfRelativeDimension (r * (G.m * G.n * Module.finrank ℚ G.F / 2) + d)
    ((GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s))⟩

end GlobalTheory.WeightTwoHeckePower
end

