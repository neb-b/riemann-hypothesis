module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.LintegralStereo
section
namespace PositivityTheory.Xgp.fib_stereo

open MeasureTheory Set GroundTheory.Heights₂.Heights.FlagBundles
open scoped ENNReal NNReal

noncomputable section

def ht (ρ : ℝ) : ℝ := (1 - ρ ^ 2) / (1 + ρ ^ 2)

def nF (a : ℂ) : Fin 3 → ℝ :=
  fun i => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def nE (a : ℂ) : E3 := WithLp.toLp 2 (nF a)

def wt (a : ℂ) : ℝ := Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2

theorem continuous_nF : Continuous nF := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [nF] <;> fun_prop (disch := (intro x; positivity))

theorem measurable_nE : Measurable nE :=
  ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_nF).measurable

theorem nE_polar {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    nE (Complex.polarCoord.symm (ρ, θ)) = spherePoint (ht ρ) θ := by
  set a := Complex.polarCoord.symm (ρ, θ) with ha
  have hn : ‖a‖ ^ 2 = ρ ^ 2 := by
    rw [ha, Complex.norm_polarCoord_symm, sq_abs]
  have hre : a.re = ρ * Real.cos θ := by rw [ha]; simp [Complex.cos_ofReal_re]
  have him : a.im = ρ * Real.sin θ := by rw [ha]; simp [Complex.sin_ofReal_re]
  have hpos : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  have hsq : Real.sqrt (1 - ht ρ ^ 2) = 2 * ρ / (1 + ρ ^ 2) := by
    rw [show 1 - ht ρ ^ 2 = (2 * ρ / (1 + ρ ^ 2)) ^ 2 by unfold ht; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  unfold nE spherePoint
  ext i
  fin_cases i
  · show 2 * a.re / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.cos θ
    rw [hre, hn, hsq]; ring
  · show 2 * a.im / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.sin θ
    rw [him, hn, hsq]; ring
  · show (1 - ‖a‖ ^ 2) / (1 + ‖a‖ ^ 2) = ht ρ
    rw [hn]; rfl

theorem ht_image : ht '' Ioi 0 = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' : (0 : ℝ) < ρ := hρ
    have hp : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
    unfold ht
    constructor
    · rw [lt_div_iff₀ hp]; nlinarith
    · rw [div_lt_one hp]; nlinarith
  · rintro ⟨h1, h2⟩
    have hq : 0 < (1 - y) / (1 + y) := div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((1 - y) / (1 + y)), Real.sqrt_pos.2 hq, ?_⟩
    unfold ht
    rw [Real.sq_sqrt hq.le]
    have : (1 : ℝ) + y ≠ 0 := by linarith
    field_simp
    ring

theorem ht_injOn : InjOn ht (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  unfold ht at hxy
  rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
  have h2 : x ^ 2 = y ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

theorem hasDerivAt_ht (ρ : ℝ) : HasDerivAt ht (-(4 * ρ) / (1 + ρ ^ 2) ^ 2) ρ := by
  have hp : (1 : ℝ) + ρ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * ρ)) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * ρ) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_add 1
  have := h1.div h2 hp
  have e : (fun x : ℝ => 1 - x ^ 2) / (fun x : ℝ => 1 + x ^ 2) = ht := by
    funext x; rfl
  rw [e] at this
  exact this.congr_deriv (by ring)

theorem lintegral_ht (G : ℝ → ℝ≥0∞) :
    ∫⁻ c in Ioo (-1 : ℝ) 1, G c =
      ∫⁻ ρ in Ioi 0, ENNReal.ofReal (4 * ρ / (1 + ρ ^ 2) ^ 2) * G (ht ρ) := by
  rw [← ht_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun ρ _ => (hasDerivAt_ht ρ).hasDerivWithinAt) ht_injOn G]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]

theorem continuous_ht : Continuous ht := by
  unfold ht
  fun_prop (disch := (intro x; positivity))

theorem lintegral_stereo (g : E3 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ a : ℂ, ENNReal.ofReal (wt a) * g (nE a) =
      (ENNReal.ofReal (4 * Real.pi))⁻¹ *
        ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) := by
  have hsp := SphereLongitudeCoordinates.continuous_spherePoint
  set F : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (p.1 * (Real.pi⁻¹ / (1 + p.1 ^ 2) ^ 2)) * g (spherePoint (ht p.1) p.2) with hF
  have hFm : Measurable F := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact hg.comp (hsp.measurable.comp
        ((continuous_ht.measurable.comp measurable_fst).prodMk measurable_snd))
  have hC : (ENNReal.ofReal (4 * Real.pi))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 •
      (ENNReal.ofReal (wt (Complex.polarCoord.symm p)) * g (nE (Complex.polarCoord.symm p))) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    obtain ⟨ρ, θ⟩ := p
    have hp1 : (0 : ℝ) < ρ := hp.1
    simp only [smul_eq_mul, hF]
    rw [nE_polar hp1.le, ← mul_assoc, ← ENNReal.ofReal_mul hp1.le]
    unfold wt
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hFm.aemeasurable,
    lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_const_mul' _ _ hC]
  refine lintegral_congr fun θ => ?_
  rw [lintegral_ht (fun c => g (spherePoint c θ)), ← lintegral_const_mul' _ _ hC]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  simp only [hF]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem toSphere_univ : (volume : Measure E3).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  have h := SphereLongitudeCoordinates.toSphere_preimage (s := (univ : Set E3)) MeasurableSet.univ
  rw [preimage_univ] at h
  rw [h]
  simp [Real.volume_Icc, Real.volume_Ioc]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, ENNReal.ofReal_ofNat]
  ring

theorem per_conv (g : E3 → ℝ≥0∞) :
    ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) =
      ∫⁻ φ in Ioc 0 (2 * Real.pi), ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) := by
  set h : ℝ → ℝ≥0∞ := fun φ => ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun φ => by
    simp only [hh, SphereLongitudeCoordinates.spherePoint_add_two_pi]
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  calc ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ)
      = ∫⁻ φ in Ioc (-Real.pi) (-Real.pi + 2 * Real.pi), h φ := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        refine lintegral_congr fun φ => ?_
        simp only [hh]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    _ = ∫⁻ b : AddCircle (2 * Real.pi), hper.lift b := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi)]
        rfl
    _ = ∫⁻ φ in Ioc 0 (0 + 2 * Real.pi), h φ := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) 0]
        rfl
    _ = _ := by rw [zero_add]

theorem map_stereo :
    (volume.withDensity fun a : ℂ => ENNReal.ofReal (wt a)).map nE =
      sphereMeasure.map (fun m : Sphere2 => (m : E3)) := by
  ext s hs
  rw [Measure.map_apply measurable_nE hs, withDensity_apply _ (measurable_nE hs),
    Measure.map_apply measurable_subtype_coe hs, sphereMeasure, Measure.smul_apply, smul_eq_mul,
    SphereLongitudeCoordinates.toSphere_preimage hs, toSphere_univ, ← per_conv,
    ← lintegral_stereo _ (measurable_one.indicator hs), ← lintegral_indicator (measurable_nE hs)]
  refine lintegral_congr fun a => ?_
  by_cases ha : nE a ∈ s <;> simp [Set.indicator, ha]

end

end PositivityTheory.Xgp.fib_stereo
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XAnTwo
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.an_two

theorem locUnif {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (s : X → X → ℂ)
    (hO : IsOpen (bdry s)ᶜ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (h : IsRegFamilyC2 A s ph phT) :
    TendstoLocallyUniformlyOn phT ph (𝓝[>] 0) (bdry s)ᶜ := by
  intro u hu x hx
  obtain ⟨j, hj⟩ := A.cover x
  set c := A.chart j with hc
  have hO' : IsOpen (c.target ∩ c.symm ⁻¹' (bdry s)ᶜ) := c.isOpen_inter_preimage_symm hO
  have hz : c x ∈ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ := by
    refine ⟨c.map_source hj, ?_⟩
    show c.symm (c x) ∈ (bdry s)ᶜ
    rw [c.left_inv hj]
    exact hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO' (c x) hz
  have hsub : Metric.closedBall (c x) (r / 2) ⊆ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hunif := (h j (Metric.closedBall (c x) (r / 2)) hsub (isCompact_closedBall _ _)).1
  refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) (r / 2), ?_, ?_⟩
  · apply nhdsWithin_le_nhds
    exact Filter.inter_mem (c.open_source.mem_nhds hj)
      ((c.continuousAt hj).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hr)))
  · filter_upwards [hunif u hu] with t ht y hy
    have e : c.symm (c y) = y := c.left_inv hy.1
    have := ht (c y) (Metric.ball_subset_closedBall hy.2)
    simp only [Function.comp] at this
    rw [← hc, e] at this
    exact this

theorem mInt_zero {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith]
  · rfl

end PositivityTheory.Xgp.an_two

theorem PositivityTheory.Xgp.t_an_two : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) := by
  intro hC e σ S d hd hdiff a w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have ht0 : 0 < S.t₀ := (S.reg (Sum.inl a)).1
  let f : ℝ → S.X → ℝ := fun t x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x
  let gT : ℝ → S.X → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then f t else 0
  obtain ⟨M, hM⟩ := (isCompact_univ (X := S.X)).exists_bound_of_continuousOn
    (projLine_continuous_of_smooth S.A (hd a)).continuousOn
  set L : S.X → ℝ := fun y => Real.log (rW S.L S.s y) with hL
  have hL1 : ∀ y, 1 ≤ L y := by
    intro y
    have h1 : Real.exp 1 ≤ rW S.L S.s y := by
      have := S.norm_le y
      simp only [rW]
      linarith
    exact (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le h1)).mpr h1
  have hphT : ∀ b, ∀ t, 0 < t → t ≤ S.t₀ → ∀ y ∉ bdry S.s,
      |S.phT b t y| ≤ |S.C| + |S.C₅| * L y := by
    intro b t ht ht' y hy
    obtain ⟨-, -, hr⟩ := S.reg b
    obtain ⟨-, hup, hlow, -⟩ := hr t ht ht'
    obtain ⟨-, -, -, hsw⟩ := S.sing b
    have h1 := (hsw y hy).1
    have h2 := hlow y hy
    have h3 := hup y
    have hL0 : 0 ≤ L y := zero_le_one.trans (hL1 y)
    have h4 : -(|S.C₅| * L y) ≤ -S.C₅ * L y := by
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self _) hL0)
    rw [abs_le]
    constructor
    · have := abs_nonneg S.C
      show -(|S.C| + |S.C₅| * L y) ≤ S.phT b t y
      linarith
    · have := le_abs_self S.C
      have := mul_nonneg (abs_nonneg S.C₅) hL0
      linarith
  set C₆ := 2 * |S.C| + 2 * |S.C₅| + |M| with hC₆
  have hcont : ∀ t, ContinuousOn (gT t) (bdry S.s)ᶜ := by
    intro t
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      have c1 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inl a)).2.2 t hp.1 hp.2).1
      have c2 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inr a)).2.2 t hp.1 hp.2).1
      have c3 := projLine_continuous_of_smooth S.A (hd a)
      exact ((c1.sub c2).sub c3).continuousOn
    · have e1 : gT t = 0 := if_neg hp
      rw [e1]
      exact continuousOn_const
  have hbound : ∀ t, ∀ y ∉ bdry S.s, |gT t y| ≤ C₆ * Real.log (rW S.L S.s y) := by
    intro t y hy
    have hLy := hL1 y
    have hC6 : 0 ≤ C₆ := by positivity
    show |gT t y| ≤ C₆ * L y
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      obtain ⟨l1, u1⟩ := abs_le.mp (hphT (Sum.inl a) t hp.1 hp.2 y hy)
      obtain ⟨l2, u2⟩ := abs_le.mp (hphT (Sum.inr a) t hp.1 hp.2 y hy)
      have a3 : |d a y| ≤ |M| := by
        have := hM y trivial
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self M)
      obtain ⟨l3, u3⟩ := abs_le.mp a3
      have m1 : |S.C| ≤ |S.C| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have m2 : |M| ≤ |M| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have hexp : C₆ * L y = 2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y := by
        rw [hC₆]
        ring
      rw [hexp, abs_le]
      constructor
      · show -(2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y) ≤
          S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y
        linarith
      · show S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y ≤
          2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y
        linarith
    · have e1 : gT t = 0 := if_neg hp
      rw [e1, Pi.zero_apply, abs_zero]
      exact mul_nonneg hC6 (zero_le_one.trans hLy)
  have hO : IsOpen (bdry S.s)ᶜ := (ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry S.sec).isOpen_compl
  have hlim : TendstoLocallyUniformlyOn gT 0 (𝓝[>] 0) (bdry S.s)ᶜ := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨t1, ht1, ev1⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inl a))) (ε / 2) (half_pos hε) x hx
    obtain ⟨t2, ht2, ev2⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inr a))) (ε / 2) (half_pos hε) x hx
    refine ⟨t1 ∩ t2 ∩ (bdry S.s)ᶜ, Filter.inter_mem (Filter.inter_mem ht1 ht2) self_mem_nhdsWithin, ?_⟩
    filter_upwards [ev1, ev2, Ioo_mem_nhdsGT ht0] with t e1 e2 htt y hy
    have e3 : gT t = f t := if_pos ⟨htt.1, htt.2.le⟩
    have hdy := hdiff a y hy.2
    have d1 := e1 y hy.1.1
    have d2 := e2 y hy.1.2
    rw [Real.dist_eq] at d1 d2
    rw [e3, Pi.zero_apply, Real.dist_eq]
    obtain ⟨p1, q1⟩ := abs_lt.mp d1
    obtain ⟨p2, q2⟩ := abs_lt.mp d2
    rw [abs_lt]
    constructor
    · show -ε < 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y)
      linarith
    · show 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y) < ε
      linarith
  have key := (hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i)) 0 gT C₆ hcont hbound hlim).2
  have hz : mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) 0 = 0 :=
    PositivityTheory.Xgp.an_two.mInt_zero _ _
  rw [hz] at key
  refine key.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
  have e1 : gT t = f t := if_pos ⟨ht.1, ht.2.le⟩
  rw [e1]
  rfl
end

