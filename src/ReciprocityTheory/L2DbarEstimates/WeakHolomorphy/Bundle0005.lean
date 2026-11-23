module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0004
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegIndep
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff Convolution

theorem mollify_eq_convolution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = (moll n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext x
  rw [convolution_eq_swap]
  simp only [mollify, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

theorem holoSmooth : HoloSmoothStatement := by
  intro n Ω f hΩ hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall x₀ (3 * r) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set g := (closedBall x₀ (3 * r)).indicator f with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_closedBall]
    exact (hf.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (3 * r))
  have hconv : ContDiff ℝ ∞ (mollify n r g) := by
    rw [mollify_eq_convolution]
    exact (moll_hasCompactSupport n hr0).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (moll_contDiff n r) hgi.locallyIntegrable
  have heq : f =ᶠ[𝓝 x₀] mollify n r g := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr0] with x hx
    rw [Metric.mem_ball] at hx
    have hx' : closedBall x r ⊆ Ω := by
      refine (Metric.closedBall_subset_closedBall' ?_).trans hsub
      linarith
    rw [← holo_eq_mollify hr0 (hf.mono hx')]
    simp only [mollify]
    congr 1
    funext y
    by_cases hy : y ∈ closedBall x₀ (3 * r)
    · simp [hg, Set.indicator_of_mem hy]
    · have h1 : r / 2 < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le] at hy
        have h2 := dist_triangle y x x₀
        have h3 : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      simp [hg, moll_eq_zero_of_lt hr0 h1]
  exact hconv.contDiffAt.congr_of_eventuallyEq heq

theorem holo_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℝ ∞ f Ω := by
  exact holoSmooth n Ω f hΩ hf

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem reg_ball {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω) (hu : Integrable u)
    (hw : WeakHolo Ω u) (c : V n) (r : ℝ) (hr : closedBall c (3 * r) ⊆ Ω) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] U := by
  by_cases hr0 : 0 < r
  · refine ⟨mollify n r u, fun x hx => ?_, ?_⟩
    · have hx' : closedBall x r ⊆ Ω := by
        refine (Metric.closedBall_subset_closedBall' ?_).trans hr
        rw [Metric.mem_ball] at hx; linarith
      exact (mollify_differentiableAt hΩ hu hw hr0 hx').differentiableWithinAt
    · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [mollify_tendsto_ae hu] with x hx hxb
      rw [Metric.mem_ball] at hxb
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mollify n t u x = mollify n r u x := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr0)] with t ht1 ht2
        have ht1' : 0 < t := ht1
        have ht2' : t < r := ht2
        refine mollify_indep hΩ hu hw ht1' hr0 ((Metric.closedBall_subset_closedBall' ?_).trans hr)
        linarith
      have h2 : Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (mollify n r u x)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
      exact tendsto_nhds_unique hx h2
  · have h0 : ball c r = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hr0)
    refine ⟨u, ?_, ?_⟩
    · rw [h0]; exact differentiableOn_empty
    · rw [h0, Measure.restrict_empty]

theorem reg : RegStatement := by
  intro n Ω u hΩ hw
  apply reg_glue hΩ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hr0 : 0 < ε / 8 := by positivity
  have h5 : closedBall x (5 * (ε / 8)) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have h4 : ball x (4 * (ε / 8)) ⊆ closedBall x (5 * (ε / 8)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h4Ω : ball x (4 * (ε / 8)) ⊆ Ω := h4.trans h5
  set u' := (closedBall x (5 * (ε / 8))).indicator u with hu'def
  have hu' : Integrable u' := by
    rw [hu'def, integrable_indicator_iff measurableSet_closedBall]
    exact hw.1.integrableOn_compact_subset h5 (isCompact_closedBall _ _)
  have hw' : WeakHolo (ball x (4 * (ε / 8))) u' := by
    refine ⟨hu'.locallyIntegrable.locallyIntegrableOn _, fun g hg v => ?_⟩
    have hzero : ∀ z, z ∉ tsupport g → dbarDir g z v = 0 := by
      intro z hz
      have h0 : fderiv ℝ g z = 0 := by
        rw [(notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq]; simp
      simp [dbarDir, h0]
    have hts : tsupport g ⊆ ball x (4 * (ε / 8)) := hg.2.2
    have hpt : ∀ z, u' z * dbarDir g z v = u z * dbarDir g z v := by
      intro z
      by_cases hz : z ∈ tsupport g
      · rw [hu'def, Set.indicator_of_mem (h4 (hts hz))]
      · simp [hzero z hz]
    have h1 := hw.2 g ⟨hg.1, hg.2.1, hts.trans h4Ω⟩ v
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts.trans h4Ω h))])] at h1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts h))])]
    simp_rw [hpt]
    exact h1
  obtain ⟨U, hU, hae⟩ := reg_ball (Ω := ball x (4 * (ε / 8))) Metric.isOpen_ball hu' hw' x (ε / 8)
    (Metric.closedBall_subset_ball (by linarith))
  refine ⟨ε / 8, hr0, (Metric.ball_subset_ball (by linarith)).trans h4Ω, U, hU, ?_⟩
  refine Filter.EventuallyEq.trans ?_ hae
  refine ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_)
  rw [hu'def, Set.indicator_of_mem (h4 (Metric.ball_subset_ball (by linarith) hz))]

end ReciprocityTheory.L2DbarEstimates.C
end

