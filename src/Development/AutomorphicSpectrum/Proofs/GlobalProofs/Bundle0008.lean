module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0007
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.FormalDegreeBessel.StatementG
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensions
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspaceStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_stable_subspace_coordinate : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by
  first | exact @GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | exact GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | (intros; apply GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GSFin

theorem finite_cohomology_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 1) := by
  intro F Ω _ _ _ _ _ l _ r S _ A _ hA _
  exact _root_.GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles _ _ A (_root_.GlobalTheory.CompanionTheory.Cocycles.finite_cocycles _ _ A hA (_root_.GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite F Ω _ (_root_.GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree F Ω S)))

end GlobalTheory.CompanionTheory.GSFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
section
namespace GlobalTheory.CompanionTheory.Glob

theorem inductionContragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k :=
  GlobalTheory.SmGL.IndDual.inductionContragredient

end GlobalTheory.CompanionTheory.Glob
end

