module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelA
section
noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

section Circle

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem circle_swap (ν : Measure X) [IsFiniteMeasure ν] (f : ℂ → X → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn (fun p : ℂ × X => f p.1 p.2) (sphere c R ×ˢ Set.univ)) {M : ℝ}
    (hM : ∀ z ∈ sphere c R, ∀ x, ‖f z x‖ ≤ M) :
    (∮ z in C(c, R), ∫ x, f z x ∂ν) = ∫ x, (∮ z in C(c, R), f z x) ∂ν := by
  have h1 : Continuous fun p : ℝ × X => f (circleMap c R p.1) p.2 :=
    hf.comp_continuous (((continuous_circleMap c R).comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨circleMap_mem_sphere c hR p.1, Set.mem_univ _⟩
  have hG : Continuous fun p : ℝ × X => deriv (circleMap c R) p.1 • f (circleMap c R p.1) p.2 := by
    simp only [deriv_circleMap]
    exact (((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const).smul h1
  have hint : Integrable (Function.uncurry fun θ x => deriv (circleMap c R) θ • f (circleMap c R θ) x)
      ((volume.restrict (Set.Ioc 0 (2 * π))).prod ν) := by
    refine Integrable.of_bound hG.aestronglyMeasurable (R * M) (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, deriv_circleMap, smul_eq_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hM _ (circleMap_mem_sphere c hR p.1) p.2) hR
  simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc ∫ θ in Set.Ioc 0 (2 * π), deriv (circleMap c R) θ • ∫ x, f (circleMap c R θ) x ∂ν
      = ∫ θ in Set.Ioc 0 (2 * π), ∫ x, deriv (circleMap c R) θ • f (circleMap c R θ) x ∂ν := by
        congr 1; ext θ; exact (integral_smul _ _).symm
    _ = _ := integral_integral_swap hint

theorem contOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {s : Set ℂ}
    (hF : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (s ×ˢ Set.univ)) {M : ℝ} (hM : ∀ z ∈ s, ∀ x, ‖F z x‖ ≤ M) :
    ContinuousOn (fun z => ∫ x, F z x ∂ν) s := by
  refine continuousOn_of_dominated (bound := fun _ => M) (fun z hz => ?_) (fun z hz => ae_of_all _ (hM z hz))
    (integrable_const M) (ae_of_all _ fun x => ?_)
  · exact (hF.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩).aestronglyMeasurable
  · exact hF.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz => ⟨hz, Set.mem_univ _⟩

theorem diffOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (U ×ˢ Set.univ)) (hd : ∀ x, DifferentiableOn ℂ (F · x) U)
    (hb : ∀ S ⊆ U, IsCompact S → ∃ M, ∀ z ∈ S, ∀ x, ‖F z x‖ ≤ M) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  let R : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hR : (0 : ℝ) < R := by show 0 < r / 2; positivity
  have hsub : closedBall z₀ R ⊆ U := (closedBall_subset_ball (show (R : ℝ) < r by show r / 2 < r; linarith)).trans hrU
  obtain ⟨M, hM⟩ := hb _ hsub (isCompact_closedBall z₀ R)
  have hsph : sphere z₀ (R : ℝ) ⊆ closedBall z₀ R := sphere_subset_closedBall
  have hcont : ContinuousOn (fun z => ∫ x, F z x ∂ν) (sphere z₀ R) :=
    contOn_integral ν F (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)) fun z hz => hM z (hsph hz)
  have hps := hasFPowerSeriesOn_cauchy_integral (hcont.circleIntegrable hR.le) (by exact_mod_cast hR)
  have key : ∀ w ∈ ball z₀ (R : ℝ), (∫ x, F w x ∂ν) =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν := by
    intro w hw
    have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere z₀ R) :=
      ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => sub_ne_zero.2 fun h => by
        rw [mem_sphere] at hz; rw [mem_ball, ← h, hz] at hw; exact lt_irrefl _ hw
    obtain ⟨B, hB⟩ := (isCompact_sphere z₀ (R : ℝ)).exists_bound_of_continuousOn hinv
    have hsw := circle_swap ν (fun z x => (z - w)⁻¹ • F z x) z₀ hR.le
      ((hinv.comp continuousOn_fst fun (p : ℂ × X) (hp : p ∈ sphere z₀ (R : ℝ) ×ˢ (Set.univ : Set X)) => hp.1).smul (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)))
      (M := B * M) fun z hz x => by
        rw [norm_smul]
        exact mul_le_mul (hB z hz) (hM z (hsph hz) x) (norm_nonneg _) ((norm_nonneg _).trans (hB z hz))
    have e1 : (∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) = ∮ z in C(z₀, R), ∫ x, (z - w)⁻¹ • F z x ∂ν :=
      circleIntegral.integral_congr hR.le fun z _ => (integral_smul _ _).symm
    rw [e1, hsw]
    have e2 : ∀ x, (∮ z in C(z₀, R), (z - w)⁻¹ • F z x) = (2 * π * I : ℂ) • F w x := fun x =>
      ((hd x).mono hsub).circleIntegral_sub_inv_smul hw
    simp only [e2, integral_smul, smul_smul]
    rw [inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  have hev : (fun z => ∫ x, F z x ∂ν) =ᶠ[𝓝 z₀]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) :=
    Filter.eventually_of_mem (ball_mem_nhds z₀ hR) key
  exact (hps.analyticAt.differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt

end Circle

theorem eqOn_right {U : Set ℂ} (hUo : IsOpen U) (hU : ∃ τ : ℝ, {z : ℂ | τ < z.re} ⊆ U) (hpc : IsPreconnected U)
    {h g : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) (hg : DifferentiableOn ℂ g U) (σ : ℝ)
    (e : ∀ z : ℂ, σ < z.re → h z = g z) : Set.EqOn h g U := by
  obtain ⟨τ, hτ⟩ := hU
  have hx : max τ σ < (((max τ σ + 1 : ℝ)) : ℂ).re := by simp
  have hxU : (((max τ σ + 1 : ℝ)) : ℂ) ∈ U := hτ (lt_of_le_of_lt (le_max_left _ _) hx)
  have ev : h =ᶠ[𝓝 (((max τ σ + 1 : ℝ)) : ℂ)] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with w hw
    exact e w (lt_of_le_of_lt (le_max_right _ _) hw)
  exact (hh.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hpc hxU ev

theorem integral_tsum_dom {ι α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ι → α → ℂ) (u : ι → ℝ) (hu : Summable u) (hF : ∀ i a, ‖F i a‖ ≤ u i)
    (hm : ∀ i, AEStronglyMeasurable (F i) μ) :
    ∫ a, ∑' i, F i a ∂μ = ∑' i, ∫ a, F i a ∂μ := by
  have hs := hu.countable_support
  have : Countable (Function.support u) := hs.to_subtype
  have h0 : ∀ i, i ∉ Function.support u → ∀ a, F i a = 0 := fun i hi a => by
    have : u i = 0 := Function.notMem_support.1 hi
    exact norm_le_zero_iff.1 (this ▸ hF i a)
  have e1 : ∀ a, ∑' i, F i a = ∑' i : Function.support u, F i a := fun a =>
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (h0 i h a)).symm
  have e2 : ∑' i, ∫ a, F i a ∂μ = ∑' i : Function.support u, ∫ a, F i a ∂μ :=
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (by simp [h0 i h])).symm
  simp_rw [e1, e2]
  have hI : ∀ i, Integrable (F i) μ := fun i => Integrable.of_bound (hm i) (u i) (ae_of_all _ (hF i))
  refine (integral_tsum_of_summable_integral_norm (ι := Function.support u) (F := fun i a => F i a) (fun i => hI i) ?_).symm
  refine ((hu.subtype _).mul_right (μ.real Set.univ)).of_nonneg_of_le
    (fun i => integral_nonneg fun _ => norm_nonneg _) fun i => ?_
  calc ∫ a, ‖F i a‖ ∂μ ≤ ∫ _, u i ∂μ := integral_mono (hI i).norm (integrable_const _) fun a => hF i a
    _ = u i * μ.real Set.univ := by simp [mul_comm]

theorem circle_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ s, a i * g i z) = ∑ i ∈ s, a i * ∮ z in C(c, R), g i z := by
  have hc : ∀ i ∈ s, Continuous fun θ => deriv (circleMap c R) θ • (a i * g i (circleMap c R θ)) := fun i hi => by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).smul (continuous_const.mul
      ((hg i hi).comp_continuous (continuous_circleMap c R) fun θ => circleMap_mem_sphere c hR θ))
  simp only [circleIntegral, Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum fun i hi => (hc i hi).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext θ; simp only [smul_eq_mul]; ring

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelB
section
noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

theorem circle_entire_mul (c : ℂ → ℂ) (hc : Differentiable ℂ c) (f : ℂ → ℂ) (s₀ : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hf : ContinuousOn f (sphere s₀ ε)) (k : ℕ) (hk : 1 ≤ k)
    (h0 : ∀ j, k < j → (∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * f z) = 0) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) = c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z := by
  obtain ⟨M, hM⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn hf
  have hps := hc.hasFPowerSeriesOnBall s₀ (R := 1) one_pos
  set p := cauchyPowerSeries c s₀ 1 with hp
  have hfc : Continuous fun θ => f (circleMap s₀ ε θ) :=
    hf.comp_continuous (continuous_circleMap s₀ ε) fun θ => circleMap_mem_sphere s₀ hε.le θ
  let T : ℕ → ℝ → ℂ := fun i θ => deriv (circleMap s₀ ε) θ •
    ((circleMap s₀ ε θ - s₀) ^ (k - 1) * ((circleMap s₀ ε θ - s₀) ^ i * p.coeff i * f (circleMap s₀ ε θ)))
  have hT : ∀ i, Continuous (T i) := fun i => by
    simp only [T, deriv_circleMap]
    exact ((continuous_circleMap 0 ε).mul continuous_const).smul
      ((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul
        (((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul continuous_const).mul hfc))
  have hsum : HasSum (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ)
      (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i _ => ε * ε ^ (k - 1) * M * (‖p i‖ * ε ^ i)) (fun i => (hT i).aestronglyMeasurable)
      (fun i => ae_of_all _ fun θ _ => ?_) (ae_of_all _ fun θ _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun θ _ => ?_)
    · have h1 : ‖circleMap s₀ ε θ - s₀‖ = ε := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
      have h2 := hM _ (circleMap_mem_sphere s₀ hε.le θ)
      simp only [T, deriv_circleMap, smul_eq_mul, norm_mul, norm_pow, h1, norm_circleMap_zero, abs_of_pos hε,
        Complex.norm_I, mul_one, ← p.norm_apply_eq_norm_coef]
      have hpos : 0 ≤ ε * ε ^ (k - 1) * (‖p i‖ * ε ^ i) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos]
    · have hr : ((ε.toNNReal : ℝ≥0) : ℝ≥0∞) < p.radius := lt_of_lt_of_le ENNReal.coe_lt_top hps.r_le
      have hs : Summable fun n => ‖p n‖ * ε ^ n := by
        simpa [Real.coe_toNNReal _ hε.le] using p.summable_norm_mul_pow hr
      exact hs.mul_left _
    · have := hps.hasSum_sub (y := circleMap s₀ ε θ) (Metric.mem_eball.2 (edist_lt_top _ _))
      simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at this
      exact ((this.mul_right (f (circleMap s₀ ε θ))).mul_left ((circleMap s₀ ε θ - s₀) ^ (k - 1))).const_smul _
  have hterm : ∀ i, ∫ θ in (0 : ℝ)..2 * π, T i θ = p.coeff i * ∮ z in C(s₀, ε), (z - s₀) ^ (k + i - 1) * f z := by
    intro i
    simp only [circleIntegral, T]
    rw [← intervalIntegral.integral_const_mul, show k + i - 1 = k - 1 + i by omega]
    congr 1; ext θ
    simp only [smul_eq_mul, pow_add]; ring
  have hc0 : p.coeff 0 = c s₀ := hps.hasFPowerSeriesAt.coeff_zero 1
  have hval : (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ) =
      fun i => if i = 0 then c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z else 0 := by
    funext i; rw [hterm]; split_ifs with h
    · subst h; rw [hc0, Nat.add_zero]
    · rw [h0 (k + i) (by omega), mul_zero]
  rw [hval] at hsum
  exact hsum.unique (hasSum_ite_eq 0 _)

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKA
section
namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

def cj {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : Matrix p m R := (M.map s)ᵀ

theorem cj_apply {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    cj s M i j = s (M j i) := rfl

theorem det_prod_transvec {K : Type} [CommRing K] (L : List (TransvectionStruct n K)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det]

theorem fieldB {K : Type} [Field K] (c d X Y : Matrix n n K) (h : c * X + d * Y = 1) :
    ∃ B : Matrix n n K, (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal d
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  set E' : Matrix n n K := diagonal fun j => 1 - D j * (D j)⁻¹ with hE'
  set N := P * c * X * P⁻¹ with hNdef
  refine ⟨X * P⁻¹ * E' * Q⁻¹, ?_⟩
  have hM : P * (d + c * (X * P⁻¹ * E' * Q⁻¹)) * Q = diagonal D + N * E' := by
    rw [Matrix.mul_add, Matrix.add_mul, hD]
    congr 1
    simp only [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.mul_one]
  have hPd : P * d = diagonal D * Q⁻¹ := by
    rw [← hD]; simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu]
  have hN : ∀ i j, D i = 0 → N i j = (1 : Matrix n n K) i j := by
    intro i j hi
    have h1 : N + P * d * Y * P⁻¹ = 1 := by
      calc N + P * d * Y * P⁻¹ = P * (c * X + d * Y) * P⁻¹ := by
              simp [hNdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
    have h2 : (P * d * Y * P⁻¹) i j = 0 := by
      rw [hPd, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, hi, zero_mul]
    have := congrFun (congrFun h1 i) j
    rw [Matrix.add_apply, h2, add_zero] at this
    exact this
  intro hdet
  have hM0 : (diagonal D + N * E').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have hME : ∀ i j, (diagonal D + N * E') i j = (if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹) := by
    intro i j
    rw [Matrix.add_apply, hE', Matrix.mul_diagonal, Matrix.diagonal_apply]
  have hpj : ∀ j, ∑ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = 0 := by
    intro j
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [hME]
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := hpj j
    simp only [mul_inv_cancel₀ hj, sub_self, mul_zero, add_zero, mul_ite, mul_zero] at this
    rw [Finset.sum_ite_eq' Finset.univ j] at this
    simpa [hj] using this
  funext j
  by_cases hj : D j = 0
  · have := hpj j
    have e : ∀ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = p i * (1 : Matrix n n K) i j := by
      intro i
      rw [hj, zero_mul, sub_zero, mul_one]
      by_cases hi : D i = 0
      · rw [hN i j hi]
        split_ifs with hij
        · subst hij; simp [hi]
        · simp
      · rw [h1 i hi]; simp
    rw [Finset.sum_congr rfl fun i _ => e i] at this
    simpa [Matrix.one_apply] using this
  · exact h1 j hj

section Cj

variable {R : Type} [CommRing R] (s : R →+* R)

theorem cj_mul {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) : cj s (M * N) = cj s N * cj s M := by
  ext i j; simp [cj, Matrix.mul_apply, mul_comm]

theorem cj_add {m p : Type} (M N : Matrix m p R) : cj s (M + N) = cj s M + cj s N := by
  ext i j; simp [cj]

theorem cj_sub {m p : Type} (M N : Matrix m p R) : cj s (M - N) = cj s M - cj s N := by
  ext i j; simp [cj]

omit [Fintype n] in
theorem cj_one : cj s (1 : Matrix n n R) = 1 := by
  ext i j; simp [cj, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cj_cj (hs : ∀ x, s (s x) = x) {m p : Type} (M : Matrix m p R) : cj s (cj s M) = M := by
  ext i j; simp [cj, hs]

omit [Fintype n] in
theorem cj_diagonal (f : n → R) : cj s (diagonal f) = diagonal fun i => s (f i) := by
  ext i j; simp [cj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem det_cj (M : Matrix n n R) : (cj s M).det = s M.det := by
  rw [cj, det_transpose, RingHom.map_det]; rfl

end Cj

theorem fieldA {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) (c d X Y : Matrix n n K)
    (h : c * X + d * Y = 1) (hl : c * cj s d = d * cj s c) :
    ∃ B : Matrix n n K, cj s B = B ∧ (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal c
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQu
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  set R' := cj s Q⁻¹ with hR'
  have hR1 : cj s Q * R' = 1 := by rw [hR', ← cj_mul, hQQ', cj_one]
  have hR2 : R' * cj s Q = 1 := by rw [hR', ← cj_mul, hQQ, cj_one]
  set d' := P * d * R' with hd'
  set H := diagonal D * cj s d' with hH
  have hH' : H = P * (c * cj s d) * cj s P := by
    rw [hH, hd', ← hD, cj_mul, cj_mul, hR', cj_cj s hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQQ, Matrix.one_mul]
  have hHh : cj s H = H := by
    rw [hH', cj_mul, cj_mul, cj_mul, cj_cj s hs, cj_cj s hs, ← hl]
    simp only [Matrix.mul_assoc]
  have hHij : ∀ i j, H i j = D i * s (d' j i) := by
    intro i j; rw [hH, Matrix.diagonal_mul]; rfl
  have hHsym : ∀ i j, H i j = s (D j) * d' i j := by
    intro i j
    have := congrFun (congrFun hHh i) j
    rw [cj_apply, hHij j i, map_mul, hs] at this
    exact this.symm
  set e : n → K := fun i => D i * (D i)⁻¹ with he
  have hse : ∀ i, s (e i) = e i := by
    intro i; by_cases h0 : D i = 0
    · simp [he, h0]
    · simp [he, h0, mul_inv_cancel₀]
  set E : Matrix n n K := diagonal e with hE
  set Dp : Matrix n n K := diagonal fun i => (D i)⁻¹ with hDp
  obtain ⟨b', hb'⟩ : ∃ b', b' = Dp * (E - E * H * E) * cj s Dp := ⟨_, rfl⟩
  have hcE : cj s E = E := by rw [hE, cj_diagonal]; congr 1; funext i; exact hse i
  have hb'h : cj s b' = b' := by
    rw [hb', cj_mul, cj_mul, cj_sub, cj_mul, cj_mul, cj_cj s hs, hcE, hHh]
    simp only [Matrix.mul_assoc]
  refine ⟨Q * b' * cj s Q, ?_, ?_⟩
  · rw [cj_mul, cj_mul, cj_cj s hs, hb'h, Matrix.mul_assoc]
  have hM : P * (d + c * (Q * b' * cj s Q)) * R' = d' + diagonal D * b' := by
    rw [Matrix.mul_add, Matrix.add_mul, hd', ← hD]
    congr 1
    simp only [Matrix.mul_assoc, hR1, Matrix.mul_one]

  have hcol : ∀ i j, D j ≠ 0 → (d' + diagonal D * b') i j = if i = j then (s (D j))⁻¹ else 0 := by
    intro i j hj
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    have hb'ij : b' i j = (D i)⁻¹ * ((if i = j then e i else 0) - e i * H i j * e j) * s ((D j)⁻¹) := by
      rw [hb', cj_diagonal, Matrix.mul_diagonal, hDp, Matrix.diagonal_mul, Matrix.sub_apply, hE,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
    rw [Matrix.add_apply, Matrix.diagonal_mul, hb'ij, map_inv₀]
    have hej : e j = 1 := by simp [he, hj]
    rw [hej, mul_one]
    by_cases hi : D i = 0
    · have hd0 : d' i j = 0 := by
        have := hHsym i j
        rw [hHij, hi, zero_mul] at this
        exact (mul_eq_zero.1 this.symm).resolve_left hsj
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hi, hd0, hij]
    · have hei : e i = 1 := by simp [he, hi]
      rw [hei, hHsym]
      split_ifs with hij
      · subst hij; field_simp; ring
      · field_simp; ring
  intro hdet
  have hM0 : (d' + diagonal D * b').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [Finset.sum_congr rfl fun i _ => by rw [hcol i j hj]] at this
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    exact (mul_eq_zero.1 this).resolve_right (inv_ne_zero hsj)
  have hpD : p ᵥ* diagonal D = 0 := by
    funext j; rw [Matrix.vecMul_diagonal]
    by_cases hj : D j = 0
    · simp [hj]
    · simp [h1 j hj]
  have hpd' : p ᵥ* d' = 0 := by
    have := hp
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul p (diagonal D) b', hpD, Matrix.zero_vecMul, add_zero] at this
    exact this
  set q := p ᵥ* P with hq
  have hqc : q ᵥ* c = 0 := by
    have e1 : q ᵥ* c ᵥ* Q = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hD]; exact hpD
    calc q ᵥ* c = q ᵥ* c ᵥ* (Q * Q⁻¹) := by rw [hQQ, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hqd : q ᵥ* d = 0 := by
    have e1 : q ᵥ* d ᵥ* R' = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]; exact hpd'
    calc q ᵥ* d = q ᵥ* d ᵥ* (R' * cj s Q) := by rw [hR2, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hq0 : q = 0 := by
    calc q = q ᵥ* (c * X + d * Y) := by rw [h, Matrix.vecMul_one]
      _ = 0 := by rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hqc, hqd]; simp
  calc p = p ᵥ* (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, ← hq, hq0, Matrix.zero_vecMul]

end PositivityTheory.Rg.Rsw.L.LGenK
end

