module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexUpperBound.OneSubSumLeProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi
public import Formalism.LocalToGlobal.AdelicCompactOpens.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalLattice.ExistsSmulMemOfLocal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LinearProgramLowerBound.LpFeasibleLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicIndex.RowMulOfMirab
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurConvolution.MapMulApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogDivSqLeDiv
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IndexUBound
section
theorem product_lowerBound : PI.IndexUBound.IndexUBound := by
  classical
  intro ι S g r y hg hy
  have h2 : ∀ v ∈ S, (2 : ℝ) ≤ g v := fun v hv => by exact_mod_cast hg v hv

  have hfac : ∀ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1) =
      (g v : ℝ) ^ (r * (r - 1) / 2) * ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) :=
    fun v hv => PI.UnitaryGroupMassFormula.IndexUBound.prod_factor _ (by linarith [h2 v hv] : (0 : ℝ) < g v).ne' r
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]

  have hQ := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod S
    (fun v => ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i)) (fun v => 1 / ((g v : ℝ) - 1))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).1)
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.1)
    (fun v hv => div_nonneg zero_le_one (by linarith [h2 v hv]))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.2)
  beta_reduce at hQ
  have hpos : 0 ≤ ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) :=
    Finset.prod_nonneg fun v _ => by positivity
  have key := mul_le_mul_of_nonneg_right
    (show 1 - y ≤ ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) by linarith) hpos
  linarith
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime
section
open NumberField

theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen
section
theorem finiteAdeleIntegers_compactOpen : Formalism.L2.Props.IntAdelesCompactOpen := PI.IntAdCpctOpenWork.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetOrd
section
theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerPerPair
section
theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatLocGlob
section
theorem latLocGlob : PI.LatLocGlob.LatLocGlob := PI.LatLocGlob.Proof.latLocGlob_core
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatMin
section
namespace PI

theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LpLower
section
theorem lp_lower_bound : PI.LpLower := PI.lpLower_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MirabIndex
section
theorem mirabolic_index : PI.MirabIndex.MirabIndex := PI.MirabolicIndex₂.mirabIndex
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhSchurConv
section
theorem schur_orthogonality_idempotent : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverPSqTail
section
theorem prime_log_over_sq_tail : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotNuSigma
section
theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
end

