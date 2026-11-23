module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsAbFactorTens
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChart

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbFactorProdRetract
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem abFactor_prod_retract : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M₁ : Submodule R (N₁ → C)) (M₂ : Submodule R (N₂ → C)), IsAbFactor p M₁ → IsAbFactor p M₂ → IsAbFactor p (tens M₁ M₂)) ∧ ∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M : Submodule R (N₂ → C)) (i : N₁ →+ N₂) (π : N₂ →+ N₁), (∀ x, π (i x) = x) → (∀ g ∈ M, (fun x => g (i (π x))) ∈ M) → IsAbFactor p M → IsAbFactor p (M.map (LinearMap.funLeft R C (i : N₁ → N₂))) :=
  @PositivityTheory.HtPt.Rg.abfac_prod

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis' | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis' | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot GlobalTheory.CompanionTheory.FreeQuotProof

theorem FreeQuotientScheme_holds : FreeQuotientScheme := by
  intro S G X _ _ hG hfree horb
  obtain ⟨Y₀, q₀, hfin, hflat, hfp, hsurj, hpb⟩ :=
    _root_.GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts _ _ (fun x => by
      obtain ⟨U, hU, hxU⟩ := horb x
      obtain ⟨V, W, hxV, hV, hW, hVW, hinv⟩ :=
        GlobalTheory.T.orbit_affine_neighbourhood G X hG x U hU hxU
      exact ⟨V, hxV,
        _root_.GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable G X hG hfree V W hV hW hVW hinv⟩)
  haveI : IsFinite q₀ := hfin
  haveI : Flat q₀ := hflat
  haveI : LocallyOfFinitePresentation q₀ := hfp
  haveI : Surjective q₀ := hsurj
  have hdesc : ∀ {Z} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ q₀ = g₂ ≫ q₀ → g₁ ≫ X.hom = g₂ ≫ X.hom := by
    intro Z g₁ g₂ hg
    rw [← hpb.lift_fst g₁ g₂ hg]
    conv_rhs => rw [← hpb.lift_snd g₁ g₂ hg]
    simp only [Category.assoc]
    first
      | exact hpb.lift g₁ g₂ hg ≫= ((Over.w _).trans (Over.w _).symm)
      | (simp only [Over.w]; try rfl)
  have key : ∀ {Y : Over S} (q : X ⟶ Y), GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q →
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfQuotient G q ∧ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q := fun _ h => ⟨h.isFppfQuotient, h⟩
  refine ⟨Over.mk (EffectiveEpi.desc q₀ X.hom hdesc),
    Over.homMk q₀ (EffectiveEpi.fac q₀ X.hom hdesc), key _ ?_⟩
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor
  refine ⟨IsPullback.of_map_of_faithful (Over.forget S) hpb, PUnit, fun _ => X.left, fun _ => q₀,
    fun _ => ⟨hflat, hfp⟩, fun y => ?_, fun _ => ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨z, hz⟩ := hsurj.surj y
  exact ⟨PUnit.unit, z, hz⟩

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end

