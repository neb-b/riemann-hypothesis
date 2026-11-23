module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_normalised_iso_pullback_mul_by_m : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by
  first | exact @GlobalTheory.KeyKa.exists_normalised_mulPull | exact GlobalTheory.KeyKa.exists_normalised_mulPull | (intros; apply GlobalTheory.KeyKa.exists_normalised_mulPull <;> assumption)
