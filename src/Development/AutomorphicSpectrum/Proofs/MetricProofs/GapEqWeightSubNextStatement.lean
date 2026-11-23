module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

local notation "coeff" m:arg P:arg => AddMonoidAlgebra.coeff P m

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  classical
  intro Ψ _ N n
  have substitution_bound (σ : Type) [Finite σ] (f : σ → MvPolynomial σ ℝ)
      (hf : ∀ i, (f i).IsHomogeneous 1) :
      ∃ C : ℝ, ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
        (aeval f Q).IsHomogeneous n ∧
          ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (aeval f Q)| ≤ C * M) := by
    let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
    let image (d : σ →₀ ℕ) := aeval f (monomial d (1 : ℝ))
    let B (d : σ →₀ ℕ) := ∑ e ∈ (image d).support, |coeff e (image d)|
    have hB (d : σ →₀ ℕ) : 0 ≤ B d := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨∑ d ∈ S, B d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
    · simpa only [one_mul] using hQ.aeval f hf
    · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      have hsub : Q.support ⊆ S := by
        intro d hd
        simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        by_contra h
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero h)
      have hcoeff (d : σ →₀ ℕ) : |coeff m (image d)| ≤ B d := by
        by_cases hm : m ∈ (image d).support
        · exact Finset.single_le_sum (f := fun e => |coeff e (image d)|)
            (fun _ _ => abs_nonneg _) hm
        · rw [notMem_support_iff.mp hm, abs_zero]
          exact hB d
      have hexpand : coeff m (aeval f Q) =
          ∑ d ∈ Q.support, coeff d Q * coeff m (image d) := by
        calc
          _ = coeff m (aeval f (∑ d ∈ Q.support, monomial d (coeff d Q))) :=
            congrArg (fun P => coeff m (aeval f P)) Q.as_sum
          _ = _ := by
            simp only [map_sum, coeff_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            have hmonomial : monomial d (coeff d Q) =
                MvPolynomial.C (coeff d Q) * monomial d (1 : ℝ) := by
              rw [C_mul_monomial, mul_one]
            rw [hmonomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul]
      rw [hexpand]
      calc
        _ ≤ ∑ d ∈ Q.support, |coeff d Q * coeff m (image d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (hcoeff d) (hM d) (abs_nonneg _) (hB d)
        _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
        _ = _ := Finset.sum_mul .. |>.symm
  have gapX_hom := @PositivityTheory.Xgp.poly_towt_bound.gapX_hom Ψ N
  obtain ⟨C1, H1⟩ := substitution_bound (Ψ × Fin N) gapX gapX_hom
  obtain ⟨C2, H2⟩ := substitution_bound (Option (Ψ × Fin N))
    (fun o => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (gapX_hom p).rename_isHomogeneous)
  refine ⟨max C1 C2, ?_, ?_⟩
  · intro Q M hQ
    obtain ⟨hHom, hBound⟩ := H1 Q M hQ
    exact ⟨hHom, fun hM m => (hBound hM m).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ((abs_nonneg _).trans (hM 0)))⟩
  · intro Q M hQ
    obtain ⟨hHom, hBound⟩ := H2 Q M hQ
    exact ⟨hHom, fun hM m => (hBound hM m).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ((abs_nonneg _).trans (hM 0)))⟩
