module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChangeOfVariablesDegree
section
set_option maxSynthPendingDepth 1

open scoped ContDiff

open MeasureTheory Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

theorem continuous_det_fderiv {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous fun x => (fderiv ℝ φ x).det := by
  have : (fun x => (fderiv ℝ φ x).det) = fun x => detCML (entriesCLM (fderiv ℝ φ x)) := by
    funext x; rw [det_fderiv_eq_det_jacobian]; rfl
  rw [this]
  exact detCML.cont.comp (entriesCLM.continuous.comp (hφ.continuous_fderiv (by simp)))

theorem hasCompactSupport_comp_sub {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (C : ℝ)
    (hC : ∀ x, ‖φ x - x‖ ≤ C) (g : (Fin n → ℝ) → ℝ) (hgc : HasCompactSupport g)
    (y₀ : Fin n → ℝ) : HasCompactSupport fun x => g (φ x - y₀) := by
  obtain ⟨r, hr⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (r + ‖y₀‖ + C))
    fun x hx => ?_
  by_contra hne
  have h1 := hr (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff] at h1
  apply hx
  rw [mem_closedBall_zero_iff]
  have h2 : ‖x‖ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by
    calc ‖x‖ = ‖(φ x - y₀) + y₀ - (φ x - x)‖ := by congr 1; abel
      _ ≤ ‖(φ x - y₀) + y₀‖ + ‖φ x - x‖ := norm_sub_le _ _
      _ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
  linarith [hC x]

theorem clm_apply_eq_sum {n : ℕ} (T : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    T v = ∑ k, v k * T (Pi.single k 1) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

variable {m : ℕ}

theorem integral_fderiv_comp_mul_det_eq_zero (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (g : (Fin (m + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det = 0 := by
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  set H : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ := fun x => Function.update (φ x) 0 (g (φ x))
    with hH
  have hH0 : (fun x => H x 0) = fun x => g (φ x) := by
    funext x; simp [hH]
  have hHk : ∀ k, k ≠ 0 → (fun x => H x k) = fun x => φ x k := by
    intro k hk; funext x; simp [hH, hk]
  have hHs : ContDiff ℝ ∞ H := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = 0
    · subst hk; rw [hH0]; exact hg.comp hφ
    · rw [hHk k hk]; exact (contDiff_apply ℝ (fun _ => ℝ) k).comp hφ
  have hHc : HasCompactSupport fun x => H x 0 := by
    rw [hH0]
    simpa using hasCompactSupport_comp_sub φ C hC g hgc 0
  have hdet : ∀ x, (fderiv ℝ H x).det =
      fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det := by
    intro x
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have hgd : DifferentiableAt ℝ g (φ x) := (hg.differentiable (by simp)) (φ x)
    set c : Fin (m + 1) → ℝ := fun k => fderiv ℝ g (φ x) (Pi.single k 1) with hc
    have hJ : Matrix.of (jacobian H x) = (Matrix.of (jacobian φ x)).updateRow 0
        (∑ k, c k • (Matrix.of (jacobian φ x)) k) := by
      ext r l
      rw [Matrix.of_apply, jacobian_eq_fderiv_apply H x ((hHs.differentiable (by simp)) x)]
      by_cases hr : r = 0
      · subst hr
        rw [hH0, Matrix.updateRow_self]
        have : fderiv ℝ (fun y => g (φ y)) x = (fderiv ℝ g (φ x)).comp (fderiv ℝ φ x) :=
          fderiv_comp x hgd hφd
        rw [this, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, hc]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [jacobian, mul_comm]
      · rw [hHk r hr, Matrix.updateRow_ne hr, Matrix.of_apply,
          jacobian_eq_fderiv_apply φ x hφd]
    rw [det_fderiv_eq_det_jacobian, hJ, Matrix.det_updateRow_sum, det_fderiv_eq_det_jacobian,
      smul_eq_mul]
  simp_rw [← hdet]
  exact integral_det_fderiv_eq_zero H hHs 0 hHc

theorem integral_comp_sub_mul_det_eq (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (f : (Fin (m + 1) → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (s : ℝ) :
    ∫ x, f (φ x - s • (Pi.single 0 1 : Fin (m + 1) → ℝ)) * (fderiv ℝ φ x).det =
      ∫ x, f (φ x) * (fderiv ℝ φ x).det := by
  set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨Cf, hCf⟩ := ((hf.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := e))).bounded_above_of_compact_support (hfc.fderiv_apply (𝕜 := ℝ) e)
  have hdc := continuous_det_fderiv φ hφ
  set Φ : ℝ → ℝ := fun s => ∫ x, f (φ x - s • e) * (fderiv ℝ φ x).det with hΦ
  have hderiv : ∀ s₀, HasDerivAt Φ 0 s₀ := by
    intro s₀
    set R := r + C + (|s₀| + 1) * ‖e‖ with hR
    set F' : ℝ → (Fin (m + 1) → ℝ) → ℝ :=
      fun s x => -(fderiv ℝ f (φ x - s • e) e) * (fderiv ℝ φ x).det with hF'
    have hbound : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        ‖F' s x‖ ≤ (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
          (fun x => Cf * |(fderiv ℝ φ x).det|) x := by
      refine Filter.Eventually.of_forall fun x s hs => ?_
      by_cases hx : x ∈ closedBall (0 : Fin (m + 1) → ℝ) R
      · rw [Set.indicator_of_mem hx]
        simp only [hF', norm_mul, norm_neg, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCf (φ x - s • e))
          (abs_nonneg _)
      · rw [Set.indicator_of_notMem hx]
        have hnot : φ x - s • e ∉ tsupport f := by
          intro hmem
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          apply hx
          rw [mem_closedBall_zero_iff]
          have hs' : |s| ≤ |s₀| + 1 := by
            rw [mem_ball, Real.dist_eq] at hs
            have := abs_sub_abs_le_abs_sub s s₀
            linarith
          have hse : ‖s • e‖ ≤ (|s₀| + 1) * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
          have h2 : ‖x‖ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by
            calc ‖x‖ = ‖(φ x - s • e) + s • e - (φ x - x)‖ := by congr 1; abel
              _ ≤ ‖(φ x - s • e) + s • e‖ + ‖φ x - x‖ := norm_sub_le _ _
              _ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
          linarith [hC' x]
        have h0 : fderiv ℝ f (φ x - s • e) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hnot (tsupport_fderiv_subset ℝ h)
        simp [hF', h0]
    have hdiff : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        HasDerivAt (fun s => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' s x) s := by
      refine Filter.Eventually.of_forall fun x s _ => ?_
      have hl : HasDerivAt (fun s : ℝ => φ x - s • e) (-e) s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_sub (φ x)
      have := (((hf.differentiable (by simp)) (φ x - s • e)).hasFDerivAt.comp_hasDerivAt s
        hl).mul_const ((fderiv ℝ φ x).det)
      refine this.congr_deriv ?_
      simp only [hF', map_neg, neg_mul]
    have hcF : ∀ s : ℝ, Continuous fun x => f (φ x - s • e) * (fderiv ℝ φ x).det := fun s =>
      (hf.continuous.comp (hφ.continuous.sub continuous_const)).mul hdc
    have hcF' : Continuous (F' s₀) :=
      (((hf.continuous_fderiv (by simp)).comp (hφ.continuous.sub continuous_const)).clm_apply
        continuous_const).neg.mul hdc
    have hcB : Continuous fun x => Cf * |(fderiv ℝ φ x).det| := continuous_const.mul hdc.abs
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s x => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' := F') (x₀ := s₀)
      (bound := (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
        fun x => Cf * |(fderiv ℝ φ x).det|)
      (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hcF s).aestronglyMeasurable)
      ((hcF s₀).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub φ C hC' f hfc _).mul_right)
      hcF'.aestronglyMeasurable
      hbound
      ((hcB.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall)
      hdiff
    have h0 : ∫ x, F' s₀ x = 0 := by
      simp only [hF', neg_mul, integral_neg]
      have hg := integral_fderiv_comp_mul_det_eq_zero φ hφ hu (fun y => f (y - s₀ • e))
        (hf.comp (contDiff_id.sub contDiff_const))
        (hfc.comp_homeomorph (Homeomorph.subRight (s₀ • e)))
      simp only [fderiv_comp_sub] at hg
      rw [hg, neg_zero]
    rw [← h0]
    exact key.2
  have hΦd : Differentiable ℝ Φ := fun s => (hderiv s).differentiableAt
  have := is_const_of_deriv_eq_zero hΦd (fun s => (hderiv s).deriv) s 0
  simpa [hΦ] using this

end ChangeOfVariablesDegree

theorem ChangeOfVariablesDegree.proof : ChangeOfVariablesDegree.Statement := by
  intro n φ hφ hu f hf hfc
  cases n with
  | zero =>
    have hid : φ = id := funext fun x => Subsingleton.elim _ _
    subst hid
    simp only [fderiv_id, id_eq, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id, mul_one]
  | succ m =>
    set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
    obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
    have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
    obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨ru, hru⟩ := hu.isCompact.isBounded.subset_closedBall 0
    have he1 : ‖e‖ = 1 := by simp [he, Pi.norm_single]
    set R := |r| + |ru| + |C| + 1 with hR
    have hpt : ∀ x, f (φ x - R • e) * (fderiv ℝ φ x).det = f (x - R • e) := by
      intro x
      have hRe : ‖R • e‖ = R := by
        rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      by_cases hx : x ∈ tsupport fun x => φ x - x
      · have hx' := hru hx
        rw [mem_closedBall_zero_iff] at hx'
        have hf1 : f (φ x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(φ x - R • e) + (φ x - x) + x‖ := by congr 1; abel
              _ ≤ ‖-(φ x - R • e) + (φ x - x)‖ + ‖x‖ := norm_add_le _ _
              _ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
                gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
          rw [hRe] at h2
          linarith [hC' x, le_abs_self r, le_abs_self ru, le_abs_self C]
        have hf2 : f (x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖x - R • e‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(x - R • e) + x‖ := by congr 1; abel
              _ ≤ ‖-(x - R • e)‖ + ‖x‖ := norm_add_le _ _
              _ = ‖x - R • e‖ + ‖x‖ := by rw [norm_neg]
          rw [hRe] at h2
          have := abs_nonneg C
          linarith [le_abs_self r, le_abs_self ru]
        rw [hf1, hf2, zero_mul]
      · rw [notMem_tsupport_iff_eventuallyEq] at hx
        have hev : φ =ᶠ[nhds x] id := hx.mono fun y hy => by simpa [sub_eq_zero] using hy
        have hfd : fderiv ℝ φ x = ContinuousLinearMap.id ℝ _ := by
          rw [hev.fderiv_eq, fderiv_id]
        have hφx : φ x = x := hev.self_of_nhds
        rw [hfd, hφx, ContinuousLinearMap.det,
          ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    calc ∫ x, f (φ x) * (fderiv ℝ φ x).det
        = ∫ x, f (φ x - R • e) * (fderiv ℝ φ x).det :=
          (ChangeOfVariablesDegree.integral_comp_sub_mul_det_eq φ hφ hu f hf hfc R).symm
      _ = ∫ x, f (x - R • e) := by simp_rw [hpt]
      _ = ∫ x, f x := integral_sub_right_eq_self f (R • e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCompactHolomorphicFibreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace CompactHolomorphicFibreFinite

theorem sum_normSq_sub {k : ℕ} (v p : Fin k → ℂ) :
    ∑ i, Complex.normSq (v i - p i) =
      ∑ i, Complex.normSq (v i) + ∑ i, Complex.normSq (p i) -
        2 * (∑ i, v i * (starRingEnd ℂ) (p i)).re := by
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_sub]

theorem proof (hCurve : NonIsolatedFibreCurve.Statement) : CompactHolomorphicFibreFinite.Statement := by
  intro k m U f y hU hf hZ
  set Z := {v | v ∈ U ∧ f v = y} with hZdef
  by_contra hinf
  have hD : derivedSet Z ⊆ Z := (isClosed_iff_derivedSet_subset Z).1 hZ.isClosed
  have hDc : IsCompact (derivedSet Z) := hZ.of_isClosed_subset (isClosed_derivedSet Z) hD
  obtain ⟨a, -, ha⟩ := hZ.isCountablyCompact.exists_accPt_of_infinite subset_rfl hinf
  let φ : (Fin k → ℂ) → ℝ := fun v => ∑ i, Complex.normSq (v i)
  have hφc : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact Complex.continuous_normSq.comp (continuous_apply i)
  obtain ⟨p, hpD, hpmax⟩ := hDc.exists_isMaxOn ⟨a, ha⟩ hφc.continuousOn
  have hpZ : p ∈ Z := hD hpD
  have hZeq : {v | v ∈ U ∧ f v = f p} = Z := by rw [hpZ.2]
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγZ⟩ :=
    hCurve k m U f p hU hf hpZ.1 (by rw [hZeq]; exact hpD)
  rw [hZeq] at hγZ

  have hγD : ∀ τ ∈ ball (0 : ℂ) r, γ τ ∈ derivedSet Z := by
    intro τ hτ
    rw [mem_derivedSet, accPt_iff_nhds]
    intro N hN
    have hτn : ball (0 : ℂ) r ∈ 𝓝 τ := isOpen_ball.mem_nhds hτ
    have hcont : ContinuousAt γ τ := hγd.continuousOn.continuousAt hτn
    have hev : ∀ᶠ s in 𝓝[≠] τ, (s ∈ ball (0 : ℂ) r ∧ γ s ∈ N) ∧ s ≠ τ :=
      (((show ∀ᶠ s in 𝓝 τ, s ∈ ball (0 : ℂ) r from hτn).and
        (show ∀ᶠ s in 𝓝 τ, γ s ∈ N from hcont hN)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨s, ⟨hs, hsN⟩, hne⟩ := hev.exists
    exact ⟨γ s, ⟨hsN, hγZ hs⟩, fun h => hne (hγi hs hτ h)⟩
  let h : ℂ → ℂ := fun τ => ∑ i, γ τ i * (starRingEnd ℂ) (p i)
  have hhd : DifferentiableOn ℂ h (ball 0 r) := by
    intro τ hτ
    refine DifferentiableWithinAt.fun_sum fun i _ => ?_
    exact (differentiableWithinAt_pi.1 (hγd τ hτ) i).mul_const _
  have hexp : ∀ τ, ∑ i, Complex.normSq (γ τ i - p i) = φ (γ τ) + φ p - 2 * (h τ).re :=
    fun τ => sum_normSq_sub (γ τ) p
  have hnn : ∀ τ, 0 ≤ ∑ i, Complex.normSq (γ τ i - p i) :=
    fun τ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hh0 : (h 0).re = φ p := by
    have e := hexp 0
    simp only [hγ0, sub_self, map_zero, Finset.sum_const_zero] at e
    linarith
  have hle : ∀ τ ∈ ball (0 : ℂ) r, (h τ).re ≤ φ p := by
    intro τ hτ
    have h1 : φ (γ τ) ≤ φ p := hpmax (hγD τ hτ)
    have h2 := hexp τ
    have h3 := hnn τ
    linarith
  have hmax : IsMaxOn (norm ∘ fun τ => Complex.exp (h τ)) (ball 0 r) 0 := by
    intro τ hτ
    simp only [Function.comp_apply, Complex.norm_exp]
    rw [hh0]
    exact Real.exp_le_exp.2 (hle τ hτ)
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) r).isPreconnected
    isOpen_ball hhd.cexp (mem_ball_self hr) hmax
  have hτ : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hre : (h ((r / 2 : ℝ) : ℂ)).re = φ p := by
    have e := congrArg (fun z : ℂ => ‖z‖) (hconst hτ)
    simp only [Function.const_apply, Complex.norm_exp] at e
    rw [← hh0]
    exact Real.exp_injective e
  have hzero : ∑ i, Complex.normSq (γ ((r / 2 : ℝ) : ℂ) i - p i) = 0 := by
    have h1 : φ (γ ((r / 2 : ℝ) : ℂ)) ≤ φ p := hpmax (hγD _ hτ)
    have h2 := hexp ((r / 2 : ℝ) : ℂ)
    have h3 := hnn ((r / 2 : ℝ) : ℂ)
    linarith
  have hγp : γ ((r / 2 : ℝ) : ℂ) = γ 0 := by
    rw [hγ0]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 hzero i
      (Finset.mem_univ i)
    exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 hi)
  have h0 := hγi hτ (mem_ball_self hr) hγp
  simp only [Complex.ofReal_eq_zero] at h0
  exact (half_pos hr).ne' h0

end CompactHolomorphicFibreFinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PExtensionQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ExtensionQuotientLength.proof : ExtensionQuotientLength.Statement := by
  intro R B _ _ _ r hinj hr hfin
  set a := Algebra.linearMap R B
  set P : Submodule R B := LinearMap.range a
  set rP : Submodule R B := Submodule.map a (Ideal.span {r})
  set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R
  have hrPP : rP ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrPrB : rP ≤ rB := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩
  have hPr : P ≤ rP.comap (r • LinearMap.id) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩

  let f₁ := (Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)
  let g₁ := rP.mapQ P LinearMap.id hrPP
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    simp only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨y, hy, hyx⟩ := hq
    rwa [← hinj hyx]
  have hg₁ : Function.Surjective g₁ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₁ : Function.Exact f₁ g₁ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ x => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      simpa using P.sub_mem (hrPP hq) ⟨x, rfl⟩

  let f₂ := P.mapQ rP (r • LinearMap.id) hPr
  let g₂ := rP.mapQ rB LinearMap.id hrPrB
  have hf₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hq ⊢
    obtain ⟨y, hy, hyb⟩ := hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩
    simpa [a, Algebra.smul_def, mul_comm] using hyb
  have hg₂ : Function.Surjective g₂ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₂ : Function.Exact f₂ g₂ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)
      exact ⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ c => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      have hc : r • c ∈ rB := Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩
      simpa using rB.sub_mem hc (hrPrB hq)
  have h₁ := Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁
  have h₂ := Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂
  rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_inj hfin).1 h₂

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatDimFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FlatDimFormula.proof : FlatDimFormula.Statement := by
  intro A B _ _ _ _ _ hA hB hloc hflat
  set I : Ideal B := (maximalIdeal A).map (algebraMap A B) with hI

  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩

  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hIle)
  have : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  rw [← hI, hmap] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B ⧸ I), key, WithBot.coe_add]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicJacobianNeZero.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      ∀ x ∈ U, LinearMap.det (fderiv ℂ f x : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

