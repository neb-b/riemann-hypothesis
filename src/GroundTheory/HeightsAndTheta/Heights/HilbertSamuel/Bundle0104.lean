module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0100
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStD

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

theorem ChartDimLt.proof : ChartDimLt.Statement := by
  intro K _ ι _ J e p hJ hdim
  have key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes,
      ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e := by
    intro Z hZ
    have : Z.IsPrime := hZ.1.1
    obtain ⟨s, hs, hle⟩ := ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2
    have hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt hle hdim
    have hlt' : s + Fintype.card K < e + Fintype.card K := by exact_mod_cast hlt
    exact ⟨s, hs, by omega⟩
  cases e with
  | zero =>
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_)
      (WithBot.bot_lt_coe _)
    obtain ⟨s, -, hs⟩ := key Z hZ
    omega
  | succ n =>
    have hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _
        fun Z hZ => ?_) hn
    obtain ⟨s, hs, hsn⟩ := key Z hZ
    rw [hs]
    exact_mod_cast (by omega : s ≤ n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

theorem VeroneseChi.proof (hB : VeroneseMonoBasis.Statement) (hG : VeroneseGramMono.Statement) :
    VeroneseChi.Statement := by
  classical
  intro D _ n
  obtain ⟨bM, hM, hMv⟩ := hB D n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Veronese.Idx D)) ℚ), IsSecBasis (Veronese.x D) n p.2 :=
    ⟨⟨_, bM⟩, hM⟩
  unfold Veronese.chi
  rw [dite_eq_left h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r', b'⟩ := p
  have hp' : IsSecBasis (Veronese.x D) n b' := hp
  have hr : r' = (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card := hp'.card_eq.trans hM.card_eq.symm
  subst hr
  have hA : ∀ k, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ l, c l • aeval (Veronese.x D) (bM l) = aeval (Veronese.x D) (b' k) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hM.2.2, ← hp'.2.2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hB' : ∀ l, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ m, c m • aeval (Veronese.x D) (b' m) = aeval (Veronese.x D) (bM l) := fun l =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hp'.2.2, ← hM.2.2]; exact Submodule.subset_span ⟨l, rfl⟩)
  choose A hA using hA
  choose B hB' using hB'
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    ext k m
    have h1 : ∑ m, (Matrix.of A * Matrix.of B) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hB']
      exact hA k
    have h2 : ∑ m, (1 : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card)
        (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp [Matrix.one_apply]
    have hli := Fintype.linearIndependent_iff.mp hp'.2.1
      (fun m => (Matrix.of A * Matrix.of B) k m - (1 : Matrix _ _ ℤ) k m)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]) m
    exact sub_eq_zero.mp hli
  have hdet : (Matrix.of A).det ^ 2 = 1 := by
    have hd := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact Int.isUnit_sq (isUnit_iff_exists_inv.mpr ⟨_, hd⟩)
  have hGb := hG D n _ b' (Matrix.of A) fun k => by
    rw [← hA k]
    simp only [hMv, zsmul_eq_mul, Matrix.of_apply]
  rw [hGb]
  have hdA : ((Matrix.of A).map (Int.cast : ℤ → ℝ)).det = ((Matrix.of A).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det (Matrix.of A)).symm
  have hdet' : ((Matrix.of A).det : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdA]
  have hprod : ((Matrix.of A).det : ℝ) * (∏ k, monoNormSq (adtEnum D (2 * n) k)) * ((Matrix.of A).det : ℝ) =
      ∏ k, monoNormSq (adtEnum D (2 * n) k) := by
    linear_combination (∏ k, monoNormSq (adtEnum D (2 * n) k)) * hdet'
  rw [hprod, Real.log_prod (fun k _ => (monoNormSq_pos (adtEnum D (2 * n) k)).ne'), chiP,
    sum_adtEnum D (2 * n) (fun a => Real.log (monoNormSq a))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

