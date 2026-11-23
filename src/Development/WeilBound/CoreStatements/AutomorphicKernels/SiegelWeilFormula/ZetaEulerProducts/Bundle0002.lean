module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.FactorDifferentiable
section
open Filter Topology Complex NumberField IsDedekindDomain

namespace PositivityTheory.Lord

theorem factor_differentiable (N : ℕ) (hN : N ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) := by
  intro s
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hN')))

theorem factor_analytic (N : ℕ) (hN : N ≠ 0) (c x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) x :=
  (PositivityTheory.Lord.factor_differentiable N hN c).analyticAt x

theorem factor_ne_zero (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_neg_of_pos hs)
  have h1 : c * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖(N : ℂ) ^ (-s)‖ ≤ 1 * ‖(N : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rwa [one_mul]
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

theorem factor_ne_zero_int (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    1 - c * (N : ℂ) ^ (-(j : ℂ)) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h1 : c * (N : ℂ) ^ (-(j : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-(j : ℂ))‖ = ‖(1 : ℂ)‖ := by rw [h1]
  rw [norm_mul, hc, one_mul, norm_one, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
    Complex.intCast_re] at hn
  rcases lt_or_gt_of_ne hj with hj' | hj'
  · have hjr : (j : ℝ) < 0 := by exact_mod_cast hj'
    have : (1 : ℝ) < (N : ℝ) ^ (-(j : ℝ)) := Real.one_lt_rpow hN1 (by linarith)
    linarith
  · have hjr : (0 : ℝ) < j := by exact_mod_cast hj'
    have : (N : ℝ) ^ (-(j : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
    linarith

theorem factor_zo (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    ZO (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) (j : ℂ) 0 :=
  PositivityTheory.Lord.ZO.of_analytic (PositivityTheory.Lord.factor_analytic N (by omega) c _)
    (PositivityTheory.Lord.factor_ne_zero_int N hN c hc j hj)

theorem factor_zo_zero (N : ℕ) (hN : 2 ≤ N) : ZO (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have han : AnalyticAt ℂ (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 := by
    simpa only [one_mul] using PositivityTheory.Lord.factor_analytic N (by omega) 1 0
  have hd : HasDerivAt (fun s : ℂ => 1 - (N : ℂ) ^ (-s))
      (-((N : ℂ) ^ (-(0 : ℂ)) * Complex.log N * (-1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).neg).const_cpow (Or.inl hN')).const_sub 1
  refine PositivityTheory.Lord.ZO.one_of_deriv han ?_ ?_
  · show 1 - (N : ℂ) ^ (-(0 : ℂ)) = 0
    rw [neg_zero, Complex.cpow_zero, sub_self]
  · rw [hd.deriv, neg_zero, Complex.cpow_zero, one_mul, mul_neg_one, neg_neg]
    intro hlog
    have h1 : (N : ℂ) = 1 := by rw [← Complex.exp_log hN', hlog, Complex.exp_zero]
    have : N = 1 := by exact_mod_cast h1
    omega

theorem two_le_absNorm (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  omega

end PositivityTheory.Lord
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.InvGammaRZo
section
open Filter Topology Complex
open scoped Real

namespace PositivityTheory.Lord

theorem invGamma_zo (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ := by
        intro z
        have h := (Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
      exact hd.analyticAt _
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]
      simp [hz0]
  | succ n ih =>
    obtain ⟨u, hu, hu0, he⟩ := ih
    have hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ)) :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_id.mul (hu.comp_of_eq h1 hx)
    · simp only [hx]
      refine mul_ne_zero ?_ hu0
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    · have ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun z : ℂ => z + 1 := continuous_id.add continuous_const
          have := (hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))
          simpa only [hx] using this
        · filter_upwards [self_mem_nhdsWithin] with z hz
          intro h
          apply hz
          have : z = -(n : ℂ) - 1 := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this]; push_cast; ring
      have h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0 := by
        refine eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)
        rw [Set.mem_compl_singleton_iff, neg_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      filter_upwards [ht.eventually he, h0] with z h1 h2
      have hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ := by
        rw [Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [hg, h1]
      push_cast
      ring

theorem invGammaR_zo (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
    have hjn : (j : ℂ) = -(2 * (n : ℂ)) := by rw [hm, hn]; push_cast; ring
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    refine ⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ) := by
        have hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2) :=
          fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)
        exact (hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)
      have h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ) := by
        have hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ) := analyticAt_id.div_const
        exact hu.comp_of_eq hc (by rw [hjn]; ring)
      exact (h1.mul h2).div_const
    · simp only
      have : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
      rw [this]
      refine div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · have ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun s : ℂ => s / 2 := continuous_id.div_const 2
          have := (hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))
          have e : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
          simpa only [e] using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h
          apply hs
          have : s = 2 * (-(n : ℂ)) := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this, hjn]; ring
      filter_upwards [ht.eventually hue] with s h1
      rw [Gammaℝ_def, mul_inv, h1, hjn]
      ring
  · have hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
    refine ⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_,
      Eventually.of_forall fun s => by simp⟩
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    refine ⟨-(n : ℤ), ?_⟩
    have : ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    exact_mod_cast this

theorem invGammaC_zo (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
  obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
  have hjn : (j : ℂ) = -(n : ℂ) := by rw [hn]; push_cast; ring
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  refine ⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) :=
      fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2
    refine ((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)
    exact mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
  · simp only
    rw [hjn]
    refine mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0
    rw [Ne, cpow_eq_zero_iff]; tauto
  · rw [hjn]
    filter_upwards [hue] with s h1
    rw [Gammaℂ_def, mul_inv, h1]
    ring

end PositivityTheory.Lord
end

