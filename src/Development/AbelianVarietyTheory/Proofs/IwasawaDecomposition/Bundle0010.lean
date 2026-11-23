module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
section
open Metric Filter Topology Set

namespace GlobalTheory.PuncturedDiscExtension

theorem analyticAt_update_of_bdd {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto F (𝓝[≠] (0:ℂ)) (𝓝 (limUnder (𝓝[≠] (0:ℂ)) F)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd
    refine isBoundedUnder_of_eventually_le (a := B + ‖F 0‖) ?_
    filter_upwards [hB] with z hz
    exact (norm_sub_le _ _).trans (by linarith)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · rw [eventually_nhdsWithin_iff] at hd ⊢
    filter_upwards [hd] with z hz hz0
    have heq : Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F) =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hz hz0).congr_of_eventuallyEq heq
  · exact continuousAt_update_same.2 ht

theorem bdd_of_re_le {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by
  set g : ℂ → ℂ := fun z => (F z - ((M:ℂ) + 1))⁻¹ with hg
  have hre : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z - ((M:ℂ)+1)).re ≤ -1 := by
    filter_upwards [hM] with z hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), F z - ((M:ℂ)+1) ≠ 0 := by
    filter_upwards [hre] with z hz h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1 ≤ ‖F z - ((M:ℂ)+1)‖ := by
    filter_upwards [hre] with z hz
    have h1 := Complex.abs_re_le_norm (F z - ((M:ℂ)+1))
    have h2 : 1 ≤ |(F z - ((M:ℂ)+1)).re| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hgd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [hd, hne] with z h1 h2
    exact (h1.sub_const _).inv h2
  have hgb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖g z‖ ≤ B := ⟨1, by
    filter_upwards [hnorm] with z hz
    simp only [hg, norm_inv]
    exact inv_le_one_of_one_le₀ hz⟩
  have ha := analyticAt_update_of_bdd hgd hgb
  set g' := Function.update g 0 (limUnder (𝓝[≠] (0:ℂ)) g) with hg'
  have hg'eq : ∀ z, z ≠ 0 → g' z = g z := fun z hz => Function.update_of_ne hz _ _
  by_cases hL : g' 0 = 0
  · exfalso
    rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
    · have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, hne, self_mem_nhdsWithin] with z h1 h2 h3
        rw [hg'eq z h3, hL] at h1
        exact inv_ne_zero h2 h1
      exact hF.exists.elim fun _ h => h
    · have hS : ∀ᶠ z in 𝓝 (0:ℂ), g' z = 0 ∨ ((g' z)⁻¹).re ≤ -1 := by
        have h0 := eventually_nhdsWithin_iff.1 hre
        filter_upwards [h0] with z hz
        by_cases hz0 : z = 0
        · left; rw [hz0]; exact hL
        · right; rw [hg'eq z hz0]; simp only [hg, inv_inv]; exact hz hz0
      have hS' : {w : ℂ | w = 0 ∨ (w⁻¹).re ≤ -1} ∈ 𝓝 (g' 0) := h hS
      rw [hL] at hS'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS'
      have hmem : ((ε/2 : ℝ) : ℂ) ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rcases hball hmem with h1 | h1
      · have : (ε/2 : ℝ) = 0 := by exact_mod_cast h1
        linarith
      · rw [← Complex.ofReal_inv, Complex.ofReal_re] at h1
        have : 0 < (ε/2)⁻¹ := inv_pos.2 (by linarith)
        linarith
  · have hpos : 0 < ‖g' 0‖ := norm_pos_iff.2 hL
    have hc : ContinuousAt g' 0 := ha.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0:ℂ), ‖g' 0‖ / 2 < ‖g' z‖ :=
      hc.norm.eventually (lt_mem_nhds (by linarith))
    refine ⟨‖(M:ℂ)+1‖ + 2 / ‖g' 0‖, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin, hne] with z h1 h2 h3
    rw [hg'eq z h2] at h1
    have hq : 0 < ‖F z - ((M:ℂ)+1)‖ := norm_pos_iff.2 h3
    have hgz : ‖g z‖ = ‖F z - ((M:ℂ)+1)‖⁻¹ := by simp only [hg, norm_inv]
    rw [hgz] at h1
    have key : ‖F z - ((M:ℂ)+1)‖ ≤ 2 / ‖g' 0‖ := by
      have h4 := mul_lt_mul_of_pos_right h1 hq
      rw [inv_mul_cancel₀ hq.ne'] at h4
      rw [le_div_iff₀ hpos]
      nlinarith
    have h5 := norm_sub_norm_le (F z) ((M:ℂ)+1)
    linarith

end GlobalTheory.PuncturedDiscExtension

namespace GlobalTheory


open GlobalTheory.PuncturedDiscExtension in
theorem holomorphic_extension_of_exp_two_pi_I_bound :
    ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r →
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) →
      (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 →
        ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧
        ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  intro H r C N hr hH hC
  have hball : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ ball (0:ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr), self_mem_nhdsWithin]
      with z h1 h2
    exact ⟨h1, h2⟩
  have hHd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z := by
    filter_upwards [hball] with z hz
    exact hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1, hz.2⟩)
  set f : ℂ → ℂ := fun z => 2 * (Real.pi:ℂ) * Complex.I * H z with hf
  have hfd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z := by
    filter_upwards [hHd] with z hz
    exact hz.const_mul _
  have hfb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ B := by
    set Gf : ℂ → ℂ := fun z => z ^ N * Complex.exp (f z) with hGf
    have hGd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Gf z := by
      filter_upwards [hfd] with z hz
      exact (differentiableAt_id.pow N).mul hz.cexp
    have hGb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖Gf z‖ ≤ B := ⟨C, by
      filter_upwards [hball] with z hz
      have h := hC z hz.1 hz.2
      show ‖z ^ N * Complex.exp (f z)‖ ≤ C
      rw [norm_mul, norm_pow, mul_comm]
      exact h⟩
    have ha := analyticAt_update_of_bdd hGd hGb
    set G' := Function.update Gf 0 (limUnder (𝓝[≠] (0:ℂ)) Gf) with hG'
    have hG'eq : ∀ z, z ≠ 0 → G' z = Gf z := fun z hz => Function.update_of_ne hz _ _
    have hnz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), G' z = 0 := by
      intro h
      have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2
        rw [hG'eq z h2] at h1
        exact mul_ne_zero (pow_ne_zero _ h2) (Complex.exp_ne_zero _) h1
      exact hF.exists.elim fun _ h => h
    obtain ⟨k, u, hu, hu0, hGu⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
    have hpos : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
    have huc : ContinuousAt u 0 := hu.continuousAt
    have hup : ∀ᶠ z in 𝓝 (0:ℂ), ‖u z‖ < ‖u 0‖ + 1 :=
      huc.norm.eventually (gt_mem_nhds (by linarith))
    have hlo : ∀ᶠ z in 𝓝 (0:ℂ), ‖u 0‖ / 2 < ‖u z‖ :=
      huc.norm.eventually (lt_mem_nhds (by linarith))
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < 1 := by
      filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz
      simpa using hz
    have hrel : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖u z‖ < ‖u 0‖ + 1 ∧
        ‖u 0‖ / 2 < ‖u z‖ ∧ z ^ N * Complex.exp (f z) = z ^ k * u z := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.and (hup.and (hlo.and hGu)))]
        with z hz hh
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hh
      refine ⟨hz, ha1, ha2, ha3, ?_⟩
      have := hG'eq z hz
      rw [ha4, sub_zero, smul_eq_mul] at this
      exact this.symm
    rcases le_or_gt N k with hk | hk
    · refine bdd_of_re_le hfd (M := Real.log (‖u 0‖ + 1)) ?_
      filter_upwards [hrel] with z hh
      obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
      have hk' : z ^ k = z ^ N * z ^ (k - N) := by rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hk', mul_assoc] at he
      have he2 : Complex.exp (f z) = z ^ (k - N) * u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
      have hn : ‖Complex.exp (f z)‖ ≤ ‖u 0‖ + 1 := by
        rw [he2, norm_mul, norm_pow]
        have : ‖z‖ ^ (k - N) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
        nlinarith [norm_nonneg (u z)]
      rw [Complex.norm_exp] at hn
      have := Real.log_le_log (Real.exp_pos _) hn
      rwa [Real.log_exp] at this
    · obtain ⟨B, hB⟩ := bdd_of_re_le (F := fun z => -f z)
        (by filter_upwards [hfd] with z hz; exact hz.neg) (M := -Real.log (‖u 0‖ / 2)) (by
        filter_upwards [hrel] with z hh
        obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
        have hN : z ^ N = z ^ k * z ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
        rw [hN, mul_assoc] at he
        have he2 : z ^ (N - k) * Complex.exp (f z) = u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
        have hn : ‖u 0‖ / 2 ≤ ‖Complex.exp (f z)‖ := by
          have : ‖u z‖ ≤ ‖Complex.exp (f z)‖ := by
            rw [← he2, norm_mul, norm_pow]
            have : ‖z‖ ^ (N - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            nlinarith [norm_nonneg (Complex.exp (f z))]
          linarith
        rw [Complex.norm_exp] at hn
        have := Real.log_le_log (by positivity) hn
        rw [Real.log_exp] at this
        simp only [Complex.neg_re]
        linarith)
      exact ⟨B, by filter_upwards [hB] with z hz; simpa only [norm_neg] using hz⟩
  obtain ⟨B, hB⟩ := hfb
  have hHb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖H z‖ ≤ B := ⟨B / (2 * Real.pi), by
    filter_upwards [hB] with z hz
    have hf' : ‖f z‖ = 2 * Real.pi * ‖H z‖ := by
      simp only [hf, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [hf'] at hz
    rw [le_div_iff₀ (by positivity)]
    linarith⟩
  have haH := analyticAt_update_of_bdd hHd hHb
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H), ?_,
    fun t _ ht => Function.update_of_ne ht _ _⟩
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    exact haH.differentiableAt.differentiableWithinAt
  · have hzd : DifferentiableAt ℂ H z :=
      hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, h0⟩)
    have heq : Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H) =ᶠ[𝓝 z] H := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hzd.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspaces
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_ker_aeval_of_eigenspaces
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases h0 : p.degree = 0
  · have hu : IsUnit p := Polynomial.isUnit_iff_degree_eq_zero.mpr h0
    have hu' : IsUnit (Polynomial.aeval T p) := hu.map _
    have hk : LinearMap.ker (Polynomial.aeval T p) = ⊥ :=
      LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1
    rw [hk]
    infer_instance
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p h0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hp hq
    have hdeg : q.natDegree < n := by
      rw [← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
        Polynomial.natDegree_X_sub_C]
      omega
    have ihq := ih _ hdeg q hq0 rfl
    have hfg : (LinearMap.ker (Polynomial.aeval T p)).FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)
      · have hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q)
            ≤ T.eigenspace a := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Module.End.mem_eigenspace_iff]
          have hx' : Polynomial.aeval T p x = 0 := hx
          rw [hq, map_mul, Module.End.mul_apply] at hx'
          simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply] at hx'
          exact sub_eq_zero.mp hx'
        haveI := hT a
        exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)
      · exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le
          (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))
    exact (Module.Finite.iff_fg).mpr hfg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfUniformlyAlmostInvariant
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem norm_sq_toLp_two_eq_integral_norm_sq {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ g g
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj'] at h
  have h2 : (∫ x, ((‖g x‖ : ℂ)) ^ 2 ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [h2] at h
  apply Complex.ofReal_injective
  rw [← h, Complex.ofReal_pow]
  rfl

theorem finiteDimensional_of_uniformly_almost_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by
  intro K _ _ _ _ _ _ _ μ _ _ _ E hE U hU hinv
  classical
  obtain ⟨β, hβ1, -, hβU, hβ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := (1 : K))) isOpen_interior
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  have hβ0 : ∀ x, 0 ≤ β x := fun x => (hβ01 x).1
  have hβU' : ∀ u, β u ≠ 0 → u ∈ U := fun u hu =>
    interior_subset (hβU (subset_tsupport _ hu))
  set c : ℝ := ∫ u, β u ∂μ with hc
  have hcpos : 0 < c := β.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1) (HasCompactSupport.of_compactSpace _) hβ0 (by simp [hβ1 (Set.mem_singleton _)])
  set L := ContinuousMap.toLp (α := K) (E := ℂ) 2 μ ℂ with hL

  let b : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => (β (p.1⁻¹ * p.2) : ℂ), by fun_prop⟩
  have hb : Continuous fun x => L (b x) := L.continuous.comp b.continuous
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : K => (fun y => L (b y)) ⁻¹' Metric.ball (L (b x)) (c / 4))
    (fun x _ => hb.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  let ι : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨f.1, hE f.1 f.2⟩
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  let Φ : E →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun j : t =>
    (innerSL ℂ (L (b j.1))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ ι
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  have hf0 : ∀ j ∈ t, inner ℂ (L (b j)) (L (ι f)) = 0 := fun j hj => by
    simpa [Φ] using congrFun hf ⟨j, hj⟩
  set g : C(K, ℂ) := ι f with hg
  let R : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => g (p.2 * p.1), by fun_prop⟩
  have hint : ∀ {V : Type} [NormedAddCommGroup V] {F : K → V}, Continuous F → Integrable F μ :=
    fun hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun u => β u • R u) μ := hint (by fun_prop)
  set T : C(K, ℂ) := ∫ u, β u • R u ∂μ with hT
  have hTx : ∀ x, T x = inner ℂ (L (b x)) (L g) := fun x => by
    rw [hT, ContinuousMap.integral_apply hi1, hL, ContinuousMap.inner_toLp,
      ← integral_mul_left_eq_self (μ := μ) (fun z => g z * (starRingEnd ℂ) (b x z)) x]
    congr 1
    ext u
    simp [R, b, mul_comm]
  have hTb : ∀ x, ‖T x‖ ≤ c / 4 * ‖L g‖ := fun x => by
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hx' : ‖L (b x) - L (b j)‖ ≤ c / 4 := by
      rw [← dist_eq_norm]; exact le_of_lt hx
    have : T x = inner ℂ (L (b x) - L (b j)) (L g) := by
      rw [inner_sub_left, hf0 j hj, sub_zero, hTx]
    rw [this]
    exact (norm_inner_le_norm _ _).trans (by gcongr)
  have hLT : ‖L T‖ ≤ c / 4 * ‖L g‖ := by
    have := Lp.norm_le_of_ae_bound (f := L T) (C := c / 4 * ‖L g‖) (by positivity)
      (by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ T] with x hx
        rw [hL, hx]; exact hTb x)
    simpa [measureUnivNNReal] using this
  have hmove : ∀ u ∈ U, ‖L (R u) - L g‖ ≤ 1 / 2 * ‖L g‖ := fun u hu => by
    have h1 := hinv f.1 f.2 u hu
    have h2 : ‖L (R u - g)‖ ^ 2 ≤ (1 / 2 * ‖L g‖) ^ 2 := by
      rw [mul_pow, hL, norm_sq_toLp_two_eq_integral_norm_sq, norm_sq_toLp_two_eq_integral_norm_sq]
      norm_num
      simpa [R, hg, ι] using h1
    rw [← map_sub]
    exact le_of_sq_le_sq h2 (by positivity)
  have hdiff : L T - c • L g = ∫ u, β u • (L (R u) - L g) ∂μ := by
    rw [hT, ← L.integral_comp_comm hi1, hc, ← integral_smul_const, ← integral_sub]
    · congr 1
      ext1 u
      rw [smul_sub, L.map_smul_of_tower]
    · exact L.integrable_comp hi1
    · exact hint (by fun_prop)
  have hdn : ‖L T - c • L g‖ ≤ c * (1 / 2 * ‖L g‖) := by
    rw [hdiff, hc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hβ0 u)]
    by_cases hu : β u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (hmove u (hβU' u hu)) (hβ0 u)
  have hfin : c * ‖L g‖ ≤ c / 4 * ‖L g‖ + c * (1 / 2 * ‖L g‖) := by
    have : ‖c • L g‖ ≤ ‖L T‖ + ‖L T - c • L g‖ := by
      simpa using norm_sub_le (L T) (L T - c • L g)
    rw [norm_smul, Real.norm_of_nonneg hcpos.le] at this
    linarith
  have hg0 : ‖L g‖ = 0 := by
    have := norm_nonneg (L g)
    nlinarith
  have hg1 : g = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ
    (by rw [map_zero]; exact norm_eq_zero.1 hg0)
  ext x
  simpa [hg, ι] using congrArg (fun h : C(K, ℂ) => h x) hg1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapMapOfOneTmulMem
section
open scoped TensorProduct

namespace GlobalTheory

theorem flat_comap_map_of_one_tmul_mem {B C R : Type} [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R)
    (h : (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R)) :
    r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  let f : B →ₗ[B] C ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap ∘ₗ Algebra.linearMap B C
  have hex := Module.Flat.rTensor_exact R (LinearMap.exact_subtype_ker_map f)
  let φ : C ⊗[B] R →ₐ[B] (C ⧸ J) ⊗[B] R :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B J) (AlgHom.id B R)
  have hle : J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) ≤
      RingHom.ker φ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    show φ (j ⊗ₜ[B] (1 : R)) = 0
    simp [φ, Algebra.TensorProduct.map_tmul, (Ideal.Quotient.eq_zero_iff_mem).2 hj]
  have h0 : LinearMap.rTensor R f ((1 : B) ⊗ₜ[B] r) = 0 := by
    have := hle h
    rw [RingHom.mem_ker] at this
    simpa [f, φ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul] using this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[B] r)).1 h0
  have key : ∀ y : (LinearMap.ker f) ⊗[B] R,
      TensorProduct.lid B R (LinearMap.rTensor R (LinearMap.ker f).subtype y) ∈
        (J.comap (algebraMap B C)).map (algebraMap B R) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul i s =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
      rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      apply Ideal.mem_map_of_mem
      have hi := i.2
      rw [LinearMap.mem_ker] at hi
      simp only [f, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hi
      exact hi
    | add a b ha hb => simpa [map_add (f := _)] using Ideal.add_mem _ ha hb
  have := key x
  rwa [hx, TensorProduct.lid_tmul, one_smul] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangular
section
open Matrix

namespace GlobalTheory

theorem GL_upperTriangular_eq_diagonal_mul_unitriangular :
    ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ,
      B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧
      U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  intro n B hB
  have hdet : B.val.det = ∏ i, B.val i i := Matrix.det_of_upperTriangular hB
  have hdet0 : B.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  have hne : ∀ i, B.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let D : GL (Fin n) ℂ :=
    ⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j := by
    intro i j
    change (diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _
    rw [diagonal_mul]
  refine ⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩
  · intro i j hij
    rw [hU, hB hij, mul_zero]
  · intro i
    rw [hU, inv_mul_cancel₀ (hne i)]

end GlobalTheory
end

