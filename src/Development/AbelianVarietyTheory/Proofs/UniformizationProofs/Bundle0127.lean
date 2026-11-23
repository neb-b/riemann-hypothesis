module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSectionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  first | exact @GlobalTheory.InducedTranslation.exists_translT_indAt | exact GlobalTheory.InducedTranslation.exists_translT_indAt | (intros; apply GlobalTheory.InducedTranslation.exists_translT_indAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperatorStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) x, QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s' := by
  first | exact @GlobalTheory.UT.symLift_acts_as_phi | exact GlobalTheory.UT.symLift_acts_as_phi | (intros; apply GlobalTheory.UT.symLift_acts_as_phi <;> assumption)
end

