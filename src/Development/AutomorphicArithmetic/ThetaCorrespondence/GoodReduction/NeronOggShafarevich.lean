module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInfiniteTorsionUnramified

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.Nos
open GlobalTheory

theorem neronOggShafarevich : NeronOggShafarevichSt := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA
  tfae_have 1 → 2 := _root_.GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction R K Ω V hV A
  tfae_have 2 → 4 := fun hb => (_root_.GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite R K Ω V A hb).1
  tfae_have 2 → 3 := fun hb => (_root_.GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite R K Ω V A hb).2
  tfae_have 4 → 3 := by
    rintro ⟨l, hf, hl, ht⟩
    exact _root_.GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified R K Ω V hV A hA l hl ht
  tfae_have 3 → 1 := UpperTheory.Lit.Nos.C6.hasGoodReduction_of_infinite_torsionUnramified R K Ω V hV A hA
  tfae_finish

end UpperTheory.Lit.Nos.Nos
