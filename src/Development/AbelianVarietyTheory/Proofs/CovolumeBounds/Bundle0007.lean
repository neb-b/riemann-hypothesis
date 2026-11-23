module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
section
namespace GlobalTheory.FormalCalc

open MvPowerSeries

variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

noncomputable def formalExp (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.exp A).subst f

noncomputable def formalLog (g : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.log A).subst (g - 1)

omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    PowerSeries.HasSubst (g - 1) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hg])

theorem constantCoeff_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  have h := constantCoeff_subst_of_zero (σ := Unit) (a := fun _ => f)
    (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (fun _ => hf) (PowerSeries.exp A)
  rw [formalExp, PowerSeries.subst, h, ← PowerSeries.constantCoeff_eq]
  simp

theorem constantCoeff_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    constantCoeff (formalLog g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp [hg]) _ PowerSeries.constantCoeff_log

theorem isUnit_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    IsUnit (formalExp f) :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalExp hf]; exact isUnit_one)

theorem pderiv_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) (i : σ) :
    pderiv (R := A) i (formalExp f) = formalExp f * pderiv (R := A) i f := by
  rw [formalExp, pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    PowerSeries.derivative_exp]

private theorem one_add_X_mul_deriv_log :
    (1 + PowerSeries.X) * PowerSeries.derivative (R := A) (PowerSeries.log A) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add (f := _)]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ]

theorem mul_pderiv_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) (i : σ) :
    g * pderiv (R := A) i (formalLog g) = pderiv (R := A) i g := by
  have hs := hasSubst_sub_one hg
  have h := congrArg (PowerSeries.substAlgHom (R := A) hs) (one_add_X_mul_deriv_log (A := A))
  rw [map_mul, map_add (f := _), map_one, PowerSeries.substAlgHom_X, add_sub_cancel,
    PowerSeries.coe_substAlgHom] at h
  rw [formalLog, pderiv_powerSeries_subst hs, ← mul_assoc, h, map_sub, pderiv_one, sub_zero,
    one_mul]

theorem eq_formalExp_of_pderiv {f u : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hu : constantCoeff u = 1) (h : ∀ i, pderiv (R := A) i u = u * pderiv (R := A) i f) :
    u = formalExp f := by
  haveI : HasUniqueDiv A := IsAddTorsionFree.of_module_rat A
  have hn : constantCoeff (-f) = 0 := by simp [hf]
  have key : ∀ v : MvPowerSeries σ A, constantCoeff v = 1 →
      (∀ i, pderiv (R := A) i v = v * pderiv (R := A) i f) → v * formalExp (-f) = 1 := by
    intro v hv hd
    refine pderiv.ext (fun i => ?_) (by simp [hv, constantCoeff_formalExp hn])
    rw [Derivation.leibniz, pderiv_formalExp hn, hd, map_neg, pderiv_one, smul_eq_mul,
      smul_eq_mul]
    ring
  exact (isUnit_formalExp hn).mul_right_cancel
    ((key u hu h).trans (key _ (constantCoeff_formalExp hf) (pderiv_formalExp hf)).symm)

theorem eq_formalLog_of_pderiv {g u : MvPowerSeries σ A} (hg : constantCoeff g = 1)
    (hu : constantCoeff u = 0) (h : ∀ i, g * pderiv (R := A) i u = pderiv (R := A) i g) :
    u = formalLog g := by
  haveI : HasUniqueDiv A := IsAddTorsionFree.of_module_rat A
  have hunit : IsUnit g := isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
  refine pderiv.ext (fun i => hunit.mul_left_cancel ?_) (by rw [hu, constantCoeff_formalLog hg])
  rw [h, mul_pderiv_formalLog hg]

@[simp] theorem formalExp_zero : formalExp (0 : MvPowerSeries σ A) = 1 :=
  (eq_formalExp_of_pderiv (by simp) (by simp) fun i => by simp).symm

@[simp] theorem formalLog_one : formalLog (1 : MvPowerSeries σ A) = 0 :=
  (eq_formalLog_of_pderiv (by simp) (by simp) fun i => by simp).symm

theorem formalLog_mul {f g : MvPowerSeries σ A} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) : formalLog (f * g) = formalLog f + formalLog g := by
  refine (eq_formalLog_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalLog hf, constantCoeff_formalLog hg]) fun i => ?_).symm
  rw [Derivation.leibniz, ← mul_pderiv_formalLog hf, ← mul_pderiv_formalLog hg, map_add (f := _),
    smul_eq_mul, smul_eq_mul]
  ring

theorem formalLog_prod {κ : Type*} (s : Finset κ) {g : κ → MvPowerSeries σ A}
    (hg : ∀ k ∈ s, constantCoeff (g k) = 1) :
    formalLog (∏ k ∈ s, g k) = ∑ k ∈ s, formalLog (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h' : ∀ j ∈ s, constantCoeff (g j) = 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.prod_insert hk, formalLog_mul
      (hg k (Finset.mem_insert_self _ _)) (by rw [map_prod]; exact Finset.prod_eq_one h'), ih h']

theorem formalLog_pow (n : ℕ) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    formalLog (g ^ n) = n • formalLog g := by
  simpa using formalLog_prod (Finset.range n) (g := fun _ => g) fun _ _ => hg

theorem subst_formalExp {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    subst a (formalExp f) = formalExp (subst a f) := by
  rw [formalExp, formalExp, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const ha]

theorem subst_formalLog {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    subst a (formalLog g) = formalLog (subst a g) := by
  rw [formalLog, formalLog, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (hasSubst_sub_one hg).const ha, subst_sub ha, subst_one' ha]

theorem map_formalLog (φ : A →+* B) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    map φ (formalLog g) = formalLog (map φ g) := by
  refine eq_formalLog_of_pderiv (by simp [hg]) (by simp [constantCoeff_formalLog hg]) fun i => ?_
  rw [pderiv_map, pderiv_map, ← map_mul, mul_pderiv_formalLog hg]

end GlobalTheory.FormalCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableOnOfNormLeSumAbsLogAddLogLog
section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real

namespace GlobalTheory

section Holomorphic

theorem log_norm_le_circleAverage_log_norm {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) : Real.log ‖g 0‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have hg' : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := by simpa using hg
  rw [hg'.circleAverage_log_norm h0, le_add_iff_nonneg_left]
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u) ?_
    rcases eq_or_ne u 0 with rfl | h
    · simp
    · refine Real.log_nonneg ?_
      have h1 : ‖u‖ ≤ 1 := by simpa using hu
      simpa using (one_le_inv₀ (norm_pos_iff.2 h)).2 h1
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private noncomputable def logGap (M : ℝ) (y : ℂ) : ℝ≥0∞ :=
  if y = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖y‖)

private theorem measurable_logGap (M : ℝ) : Measurable (logGap M) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem lintegral_logGap_circle_le {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) {M : ℝ} (hM : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t)) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hne : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), g (circleMap 0 1 t) ≠ 0 := by
    have h1 := hg.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one)
      (isConnected_closedBall zero_le_one)
    have h3 : g ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|) :=
      codiscreteWithin_mono (by simpa using sphere_subset_closedBall) h1
    exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
      (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete one_ne_zero h3))
  have hint : IntegrableOn (fun t => Real.log ‖g (circleMap 0 1 t)‖) (Ioc 0 (2 * π)) := by
    have h1 : CircleIntegrable (fun z => Real.log ‖g z‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm
        (hg.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2.le).1 h1
  have hc : IntegrableOn (fun _ : ℝ => Real.log M) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hJ := log_norm_le_circleAverage_log_norm hg h0
  rw [Real.circleAverage, intervalIntegral.integral_of_le h2.le, smul_eq_mul,
    le_inv_mul_iff₀ h2] at hJ
  calc ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t))
      = ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (Real.log M - Real.log ‖g (circleMap 0 1 t)‖) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hne] with t ht
        simp [logGap, ht]
    _ = ENNReal.ofReal (∫ t in Ioc 0 (2 * π), (Real.log M - Real.log ‖g (circleMap 0 1 t)‖)) := by
        refine (ofReal_integral_eq_lintegral_ofReal (hc.sub hint) ?_).symm
        filter_upwards [hne] with t ht
        exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 ht)
          (hM _ (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t))))
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_sub hc hint]
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul]
        linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_log_norm_ball_zero (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r)) (hM : ∀ z ∈ ball (0 : E) r, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball 0 r) μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set F : E → ℂ := (ball (0 : E) r).piecewise f 0 with hF
  have hFm : Measurable F :=
    hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_ball
  set G : E → ℝ≥0∞ := (ball (0 : E) r).indicator fun z => logGap M (F z) with hG
  have hGm : Measurable G := ((measurable_logGap M).comp hFm).indicator measurableSet_ball
  have hj : Measurable fun p : ℝ × E => G (circleMap 0 1 p.1 • p.2) := by
    refine hGm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in ball 0 r, logGap M (F z) ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, G (circleMap 0 1 t • z) ∂μ = ∫⁻ z in ball 0 r, logGap M (F z) ∂μ :=
      fun t => by
        rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hGm, hG,
          lintegral_indicator measurableSet_ball]
    simp [h4]
  have hsm : ∀ z ∈ ball (0 : E) r, ∀ c ∈ closedBall (0 : ℂ) 1, c • z ∈ ball (0 : E) r := by
    intro z hz c hc
    rw [mem_ball_zero_iff] at hz ⊢
    rw [mem_closedBall_zero_iff] at hc
    calc ‖c • z‖ ≤ 1 * ‖z‖ := by rw [norm_smul]; gcongr
      _ < r := by simpa using hz
  have hB : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ < ∞ := by
    rw [lintegral_lintegral_swap hj.aemeasurable]
    calc ∫⁻ z, ∫⁻ t in Ioc 0 (2 * π), G (circleMap 0 1 t • z) ∂volume ∂μ
        ≤ ∫⁻ z, (ball (0 : E) r).indicator
          (fun _ => ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖f 0‖))) z ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : E) r
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = logGap M (f (circleMap 0 1 t • z)) :=
              fun t => by
                have := hsm z hz _ (mem_closedBall_zero_iff.2 (hn t).le)
                rw [hG, indicator_of_mem this, hF, piecewise_eq_of_mem _ _ _ this]
            have h6 : AnalyticOnNhd ℂ (fun c : ℂ => f (c • z)) (closedBall 0 1) := by
              have ho : IsOpen ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                isOpen_ball.preimage (by fun_prop)
              have hd : DifferentiableOn ℂ (fun c : ℂ => f (c • z))
                  ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                hf.comp (by fun_prop) (mapsTo_preimage _ _)
              exact (hd.analyticOnNhd ho).mono fun c hc => hsm z hz c hc
            simp only [indicator_of_mem hz, h5]
            simpa using lintegral_logGap_circle_le h6 (by simpa using h0)
              (fun c hc => hM _ (hsm z hz c hc))
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = 0 := fun t => by
              rw [hG, indicator_of_notMem]
              simpa [norm_smul, hn] using hz
            simp [h5]
      _ < ∞ := by
          rw [lintegral_indicator_const measurableSet_ball]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  rw [hA] at hB
  have hC : ∫⁻ z in ball 0 r, logGap M (F z) ∂μ < ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left hB.ne (ENNReal.ofReal_pos.2 h2).ne')
  have hFf : F =ᵐ[μ.restrict (ball 0 r)] f :=
    piecewise_ae_eq_restrict measurableSet_ball.nullMeasurableSet
  have hne : ∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0 := by
    filter_upwards [ae_lt_top ((measurable_logGap M).comp hFm) hC.ne, hFf] with z hz hz' h
    simp [hz', logGap, h] at hz
  refine ⟨hne, ?_⟩
  have hmeas : AEStronglyMeasurable (fun z => Real.log ‖f z‖) (μ.restrict (ball 0 r)) := by
    have : AEMeasurable f (μ.restrict (ball 0 r)) := ⟨F, hFm, hFf.symm⟩
    exact (Real.measurable_log.comp_aemeasurable this.norm).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : E => Real.log M) (ball 0 r) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hsub : IntegrableOn (fun z => Real.log M - Real.log ‖f z‖) (ball 0 r) μ := by
    refine ⟨aestronglyMeasurable_const.sub hmeas, ?_⟩
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hC
    filter_upwards [hne, hFf, ae_restrict_mem measurableSet_ball] with z hz hz' hzb
    rw [hz', logGap, ite_eq_right hz, Real.eNorm_eq_ofReal]
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hz) (hM z hzb))
  exact (hc.sub hsub).congr (Eventually.of_forall fun z => by simp)

theorem integrableOn_log_norm_ball (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ} {a : E}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball a r)) (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M)
    (h0 : f a ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball a r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : MapsTo (fun z : E => z + a) (ball 0 r) (ball a r) := fun z hz => by simpa using hz
  obtain ⟨h1, h2⟩ := integrableOn_log_norm_ball_zero μ (f := fun z => f (z + a)) (r := r) (M := M)
    (hf.comp (by fun_prop) hm) (fun z hz => hM _ (hm hz)) (by simpa using h0)
  have hp : MeasurePreserving (fun z : E => z - a) (μ.restrict (ball a r))
      (μ.restrict (ball 0 r)) := by
    have := (measurePreserving_sub_right μ a).restrict_preimage (s := ball 0 r) measurableSet_ball
    convert this using 2
    ext z
    simp [dist_eq_norm]
  refine ⟨?_, ?_⟩
  · simpa using hp.quasiMeasurePreserving.ae h1
  · simpa [Function.comp_def, IntegrableOn] using hp.integrable_comp_of_integrable h2

theorem exists_integrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {x : E} (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z) (hx : ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := by
  have hb : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ ‖f x‖ + 1 :=
    (hf.self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono
      fun _ h => h.le
  obtain ⟨R, hR, hB⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hb)
  obtain ⟨a, ha, hax⟩ := (hx.and_eventually (ball_mem_nhds x (by positivity : 0 < R / 3))).exists
  have h1 : ball a (2 * R / 3) ⊆ ball x R := ball_subset_ball' (by linarith)
  have h2 : ball x (R / 3) ⊆ ball a (2 * R / 3) :=
    ball_subset_ball' (by rw [dist_comm] at hax; linarith)
  obtain ⟨h3, h4⟩ := integrableOn_log_norm_ball μ (f := f) (a := a) (r := 2 * R / 3)
    (fun z hz => (hB z (h1 hz)).1.differentiableWithinAt) (fun z hz => (hB z (h1 hz)).2) ha
  exact ⟨R / 3, by positivity, ae_restrict_of_ae_restrict_of_subset h2 h3, h4.mono_set h2⟩

theorem exists_integrableOn_log_norm_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {g h : E → ℂ} {x : E} (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z) (hg0 : ∃ᶠ z in 𝓝 x, g z ≠ 0)
    (hh0 : ∃ᶠ z in 𝓝 x, h z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), g z ≠ 0 ∧ h z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖g z / h z‖) (ball x r) μ := by
  obtain ⟨r, hr, h1, h2⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hg hg0
  obtain ⟨s, hs, h3, h4⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hh hh0
  have e1 : ball x (min r s) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have e2 : ball x (min r s) ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  have h5 := (ae_restrict_of_ae_restrict_of_subset e1 h1).and
    (ae_restrict_of_ae_restrict_of_subset e2 h3)
  refine ⟨min r s, lt_min hr hs, h5, ((h2.mono_set e1).sub (h4.mono_set e2)).congr ?_⟩
  filter_upwards [h5] with z hz
  simp [Real.log_div, hz.1, hz.2]

end Holomorphic

section Coordinates

open Bornology

variable {ι : Type*} [Fintype ι]

variable {F : Type*} [NormedAddCommGroup F]

end Coordinates

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralLogNormLeHalfLogIntegralSq
section
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise

namespace GlobalTheory

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Function.uncurry (sphereRotation (E := E))) =
      fun q : ℝ × sphere (0 : E) 1 => circleMap 0 1 q.1 • (q.2 : E) := by
    funext q
    exact coe_sphereRotation q.1 q.2
  rw [e]
  exact ((continuous_circleMap 0 1).comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by
  set ζ : ℂ := circleMap 0 1 θ with hζ_def
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_circleMap_zero]
  have hζ0 : ζ ≠ 0 := by
    rw [← norm_ne_zero_iff, hζ]; exact one_ne_zero
  have hm : Measurable (sphereRotation (E := E) θ) :=
    (continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' μ (hm hs), Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation θ ⁻¹' s) : Set E) =
      (fun v : E => ζ • v) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereRotation θ w, hw, rfl⟩, ?_⟩
      show t • ((sphereRotation θ w : sphere (0 : E) 1) : E) = ζ • (t • (w : E))
      rw [coe_sphereRotation]
      exact smul_comm t ζ (w : E)
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, huv⟩
      have hwmem : ζ⁻¹ • (u : E) ∈ sphere (0 : E) 1 := by
        simp [norm_smul, hζ]
      set w : sphere (0 : E) 1 := ⟨ζ⁻¹ • (u : E), hwmem⟩ with hw_def
      have hw : sphereRotation θ w = u := by
        apply Subtype.ext
        rw [coe_sphereRotation]
        show ζ • ζ⁻¹ • (u : E) = u
        rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      refine ⟨t, ht, _, ⟨w, ?_, rfl⟩, ?_⟩
      · show sphereRotation θ w ∈ s
        rw [hw]; exact hu
      · have huv' : t • (u : E) = ζ • v := huv
        show t • (ζ⁻¹ • (u : E)) = v
        rw [smul_comm t ζ⁻¹, huv', smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [hset]
  exact (measurePreserving_smul_of_norm_eq_one μ hζ).measure_preimage_emb
    (MeasurableEquiv.smul₀ ζ hζ0).measurableEmbedding _

end Rotation

section Torus

variable {ι : Type*} [Fintype ι]

end Torus

section Concavity

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

end Concavity

end GlobalTheory
end

