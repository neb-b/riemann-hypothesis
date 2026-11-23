module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0001
public import Formalism.DegreeFormula.PointDegree.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithFunctionalLipschitzWeights
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linA_pow_continuous_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) :=
  @RootFieldNumerics.linear_root_power_lipschitz

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DominantPartialSumBounds
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem partialSum_sub_mean_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| :=
  RootFieldNumerics.partial_sum_ordered_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testForms_sh_tot : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 :=
  RootFieldNumerics.exists_degree_one_class

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeSymmetries
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_integral_permutations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F :=
  @RootFieldNumerics.degFl_symmetry_invariance

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_eq_weyl : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (lam : Wt Ψ N), flagDeg lam = ((dimFl Ψ N).factorial : ℝ) * ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) ∧ (RegDominant lam → 0 < flagDeg lam) ∧ (Dominant lam → 0 ≤ flagDeg lam) := by
  intro Ψ _ _ N lam
  have hf : flagDeg lam = ((dimFl Ψ N).factorial : ℝ) *
      ∏ τ, ∏ i : Fin N, ∏ k : Fin N,
        (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) :=
    Formalism.DegreeFormula.flagDegFormula_statement Ψ N lam
  have hD : (0 : ℝ) < ((dimFl Ψ N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hki : ∀ i k : Fin N, i < k → (0 : ℝ) < (k : ℝ) - (i : ℝ) := by
    intro i k h
    have h' : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
    exact sub_pos.mpr h'
  refine ⟨hf, fun hr => ?_, fun hd => ?_⟩
  · rw [hf]
    refine mul_pos hD (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k _ => ?_)
    split_ifs with h
    · exact div_pos (sub_pos.mpr (hr τ i k h)) (hki i k h)
    · exact one_pos
  · rw [hf]
    refine mul_nonneg hD.le (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
      Finset.prod_nonneg fun k _ => ?_)
    split_ifs with h
    · exact div_nonneg (sub_nonneg.mpr (hd τ i k h.le)) (hki i k h).le
    · exact zero_le_one

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem polarisation_functional : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| :=
  @RootFieldNumerics.polarization_coefficients_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

