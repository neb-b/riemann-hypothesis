module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.Bundle0001
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0064

@[expose] public section

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
open GlobalTheory.CompanionTheory.KLowSpan (kLowSpan KLower)
open PI.UpqRep (root)

noncomputable section

namespace UpperTheory.Lit.Bur.KShift

variable {n : ℕ} {ε : Fin n → Bool}

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}

theorem kUnit_of (hU : IsUnitary ε E) : KUnit ε E := by
  intro a b hab y z
  have := hU a b y z
  simpa [Formalism.REAL.sgn, hab] using this

theorem exists_weight (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ ν : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x :=
  _root_.UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight hE hU hQ hQ0

theorem exists_highest (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ μ : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ KHighest ε E μ x := by
  classical
  let ht : (Fin n → ℝ) → ℝ := fun ν => ∑ c : Fin n, ((c : ℕ) : ℝ) * ν c
  let h : Module.End ℂ V := ∑ c : Fin n, (((c : ℕ) : ℝ) : ℂ) • E c c
  have hhQ : ∀ w ∈ Q, h w ∈ Q := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Q.sum_mem fun c _ => Q.smul_mem _ (hQ c c rfl w hw)
  have hh : ∀ (ν : Fin n → ℝ) (x : V), IsWeight E ν x → h x = ((ht ν : ℝ) : ℂ) • x := by
    intro ν x hx
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hx _, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℝ := {t | ∃ ν : Fin n → ℝ, ht ν = t ∧ ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhQ)
    refine (hfin.preimage (f := fun t : ℝ => (t : ℂ)) Complex.ofReal_injective.injOn).subset ?_
    rintro t ⟨ν, rfl, x, hxQ, hx0, hx⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxQ⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh ν x hx)
    · exact fun h0 => hx0 (congrArg Subtype.val h0)
  obtain ⟨ν₀, x₀, hx₀Q, hx₀, hx₀w⟩ := exists_weight hE hU hQ hQ0
  have hSne : S.Nonempty := ⟨_, ν₀, rfl, x₀, hx₀Q, hx₀, hx₀w⟩
  obtain ⟨t, ⟨ν, rfl, x, hxQ, hx0, hx⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨ν, x, hxQ, hx0, hx, fun a b hab he => ?_⟩
  by_contra hne
  have hmem : ht (ν + root a b) ∈ S :=
    ⟨_, rfl, E a b x, hQ a b he x hxQ, hne, GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hx a b⟩
  have h1 : ht (ν + root a b) = ht ν + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [GlobalTheory.CompanionTheory.DSHighestOfKType.height_root]
  have h2 := hmin _ hmem
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [id] at h2
  linarith

end Alg

section Rep

open CompanionTheory.D.DSIC (IsSmMod hStabLink hWtLink hLowSpan hHWofType hSmMod)
open PI.UpqRep (IsKTypeOf IsKStableOn IsURepOn UJset)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Sm : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ Sm}

end Rep


end UpperTheory.Lit.Bur.KShift
