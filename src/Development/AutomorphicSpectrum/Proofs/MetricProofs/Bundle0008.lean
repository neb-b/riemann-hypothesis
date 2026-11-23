module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PoissonIntegralPuncturedDisc
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PuncturedDisc

theorem le_zero_of_bddAbove_punctured (g : ℂ → ℝ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hc : ContinuousOn g {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hh : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt g z)
    (h0 : ∀ z : ℂ, ‖z‖ = ρ → g z ≤ 0)
    (hC : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → g z ≤ C) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → g w ≤ 0 := by
  intro w hw0 hwρ
  have hlogw : Real.log ‖w‖ < Real.log ρ := Real.log_lt_log hw0 hwρ
  have hD : 0 < Real.log ρ - Real.log ‖w‖ := sub_pos.mpr hlogw
  have key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖) := by
    intro ε hε
    have hexp_pos : 0 < Real.exp (-(|C| / ε)) := Real.exp_pos _
    have hexp_le : Real.exp (-(|C| / ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
      linarith
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2 := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr_def]
      exact div_pos (mul_pos hw0 hexp_pos) two_pos
    have hrw : r < ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp_le hw0.le
      rw [hr_def]
      linarith
    have hrρ : r < ρ := lt_trans hrw hwρ
    have hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2 := by
      rw [hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero,
        Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]
      ring
    let h : ℂ → ℝ := fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)
    have hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} :=
        fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩
      refine (hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))
      refine ContinuousOn.log continuous_norm.continuousOn ?_
      intro z hz
      exact (lt_of_lt_of_le hr0 hz.1).ne'
    have hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr0 hz1
      have hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)
      have hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z :=
        InnerProductSpace.harmonicAt_const _
      have h2 : InnerProductSpace.HarmonicAt
          (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z := by
        apply InnerProductSpace.HarmonicAt.const_smul
        exact hcst.sub hlog
      exact (hh z hz0 hz2).sub h2
    have hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hgz : g z ≤ C := hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)
        have hCabs : C ≤ |C| := le_abs_self C
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, hlogr]
        have e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) =
            ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2 := by ring
        have e2 : ε * (|C| / ε) = |C| := by field_simp
        rw [e1, e2]
        linarith [mul_pos hε hD, mul_pos hε hlog2]
      · show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, sub_self, mul_zero, sub_zero]
        exact h0 z hz
    have hmax := _root_.GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le
    simp only [h] at hmax
    linarith
  by_contra hneg
  have hpos := not_le.mp hneg
  have hk := key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))
  have e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
  linarith

theorem poisson_formula_punctured (f : ℂ → ℝ) (ρ R M : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → InnerProductSpace.HarmonicAt f z)
    (hB : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → |f z| ≤ M) (w : ℂ) (hw0 : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    ∫ t, pker ρ w t * f (circleMap 0 ρ t) ∂angMeas = f w := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  have hfc : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      linarith
    exact (hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt
  have hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hup := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M
    have hlo := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)
    have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x := by
      intro x hx
      rw [hρabs] at hx
      have hx' : ‖x‖ = ρ := by simpa using hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx'
        linarith
      exact ⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩
    have h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).2
        have : 0 ≤ poissonKernel 0 z x * (M - f x) := mul_nonneg hk (by linarith)
        linarith
    have h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ =
        -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ := by
      simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
    have h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).1
        exact mul_nonneg hk (by linarith)
    rw [abs_le]
    constructor <;> linarith
  let Φ : ℂ → ℝ := fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z
  have hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      have : ‖y‖ < ρ := by simpa using hy
      simp only [Φ, if_pos this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr
      (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)
  have hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ) := by
    intro z hz
    by_cases hzl : ‖z‖ < ρ
    · exact (hPharm z hzl).1.continuousAt.continuousWithinAt
    · have hzle : ‖z‖ ≤ ρ := by simpa using hz
      have hzeq : ‖z‖ = ρ := le_antisymm hzle (not_lt.mp hzl)
      have hzs : z ∈ Metric.sphere (0 : ℂ) ρ := by simpa using hzeq
      have hΦz : Φ z = f z := by simp only [Φ, if_neg hzl]
      rw [← Metric.ball_union_sphere]
      apply ContinuousWithinAt.union
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have : ‖y‖ < ρ := by simpa using hy
        simp only [Φ, if_pos this]
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (hfc z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : ‖y‖ = ρ := by simpa using hy
        simp only [Φ, if_neg (not_lt.mpr hy'.ge)]
  have hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z := by
    intro z hz
    simp only [Φ, if_neg (not_lt.mpr hz.ge)]
  have hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ := fun z hz => by
    simpa using hz.2
  have hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} := fun z hz =>
    (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt
  have hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M := by
    intro z hz0 hzρ
    by_cases hzl : ‖z‖ < ρ
    · simp only [Φ, if_pos hzl]
      exact hPbd z hzl
    · simp only [Φ, if_neg hzl]
      exact hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)
  have hA := le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ
    (hfS.sub (hΦcont.mono hS))
    (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hA' := le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ
    ((hΦcont.mono hS).sub hfS)
    (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by simp only [Φ, if_pos hwρ]
  have hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by linarith
  rw [hfw]
  have hint := GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ
  exact hint

end GlobalTheory.CompanionTheory.Ar.PuncturedDisc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminant
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_local_log_of_commutative_law : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  intro n g b₀ μ hμ hunit hcomm hassoc
  have hμ0 : μ (b₀, 0, 0) = 0 := hunit.self_of_nhds.1

  set G : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ p - p.2.1 - p.2.2 with hG
  have hGan : AnalyticAt ℂ G (b₀, 0, 0) :=
    (hμ.sub (analyticAt_fst.comp_of_eq analyticAt_snd rfl)).sub (analyticAt_snd.comp_of_eq analyticAt_snd rfl)
  have hG0 : G (b₀, 0, 0) = 0 := by simp [hG, hμ0]
  have hGsmall : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), ‖G p‖ < 1 := by
    filter_upwards [hGan.continuousAt (ball_mem_nhds (G (b₀, 0, 0)) one_pos)] with p hp
    simpa [hG0] using hp
  obtain ⟨R₁, hR₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 (hGsmall.and hGan.eventually_analyticAt)
  obtain ⟨R₂, hR₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.1 hunit
  set R := min R₁ R₂ with hRdef
  have hR : 0 < R := lt_min hR₁ hR₂
  have hRG : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖G (b, s, t)‖ < 1 ∧ AnalyticAt ℂ G (b, s, t) := by
    intro b hb s hs t ht
    refine hball₁ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hb, ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_left _ _) ht⟩
  have hRu : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, μ (b, s, 0) = s ∧ μ (b, 0, s) = s := by
    intro b hb s hs
    refine hball₂ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hb, ball_subset_ball (min_le_right _ _) hs⟩
  have hGbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
    refine GlobalTheory.T.analytic_group_law_bounded_commutator b₀ G R hR ?_ ?_ ?_
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).2.differentiableAt.differentiableWithinAt
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).1.le
    · intro b hb s hs
      have := hRu b hb s hs
      simp [hG, this.1, this.2]
  set C : ℝ := 1 / R ^ 2 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ := by
    intro b hb s hs t ht
    refine (hGbound b hb s hs t ht).trans (le_of_eq ?_)
    rw [hCdef]; ring
  set d : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ (p.1, p.2, p.2) with hd
  have hdan : AnalyticAt ℂ d (b₀, 0) := by
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (p.1, p.2, p.2)) (b₀, 0) :=
      analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd)
    exact AnalyticAt.comp_of_eq hμ h1 rfl
  have hd0 : d (b₀, 0) = 0 := hμ0
  have hdderiv : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) (b₀, 0) := by
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hmem : ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) (min R (c / C)) ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      ball_mem_nhds _ (lt_min hR (by positivity))
    filter_upwards [hmem] with p hp
    obtain ⟨b, s⟩ := p
    rw [← ball_prod_same] at hp
    obtain ⟨hb, hs⟩ := hp
    have hb' : b ∈ ball b₀ R := ball_subset_ball (min_le_left _ _) hb
    have hs' : s ∈ ball (0 : Fin g → ℂ) R := ball_subset_ball (min_le_left _ _) hs
    have h1 := hbound b hb' s hs' s hs'
    have hsn : ‖s‖ < c / C := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have heq : d (b, s) - d (b₀, 0) - ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) ((b, s) - (b₀, 0)) = μ (b, s, s) - s - s := by
      rw [hd0]
      simp [hd, two_smul]
      abel
    rw [heq]
    have hle : ‖s‖ ≤ ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by
      simp [Prod.norm_def]
    have hCs : C * ‖s‖ ≤ c := ((lt_div_iff₀' hCpos).1 hsn).le
    calc ‖μ (b, s, s) - s - s‖ ≤ C * ‖s‖ * ‖s‖ := h1
      _ ≤ c * ‖s‖ := by gcongr
      _ ≤ c * ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by gcongr
  obtain ⟨h, hhan, hh0, H1, H2⟩ := GlobalTheory.T.analytic_doubling_map_local_inverse b₀ d hdan hd0 hdderiv
  have hmed := LocalLog.medial_eventually b₀ μ hμ.continuousAt hμ0 hcomm hassoc
  have hhc : ContinuousAt h (b₀, 0) := hhan.continuousAt
  have t0 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
    continuous_fst.tendsto _
  have t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_fst.comp continuous_snd).tendsto _)
  have t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_snd.comp continuous_snd).tendsto _)
  have ts : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t1
  have tt : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t2
  have t3 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, h (p.1, p.2.1), h (p.1, p.2.2))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0, 0)) :=
    t0.prodMk_nhds (ts.prodMk_nhds tt)
  have t4 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds (by simpa [Function.comp_def, hμ0] using hμ.continuousAt.tendsto.comp t3)
  have hhom : ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), h (p.1, μ p) = μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)) := by
    filter_upwards [t1.eventually H1, t2.eventually H1, t3.eventually hmed, t4.eventually H2] with p e1 e2 e3 e4
    obtain ⟨b, s, t⟩ := p
    have e1' : μ (b, h (b, s), h (b, s)) = s := e1
    have e2' : μ (b, h (b, t), h (b, t)) = t := e2
    have e3' : μ (b, μ (b, h (b, s), h (b, s)), μ (b, h (b, t), h (b, t))) = μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t))) := e3
    have e4' : h (b, μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))) = μ (b, h (b, s), h (b, t)) := e4
    rw [e1', e2'] at e3'
    show h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))
    rw [e3', e4']
  have hsmall : ∀ᶠ q in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), ‖h q‖ < min R (1 / (3 * C)) := by
    have hpos : 0 < min R (1 / (3 * C)) := lt_min hR (by positivity)
    filter_upwards [hhc (ball_mem_nhds (h (b₀, 0)) hpos)] with p hp
    simpa [hh0] using hp
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 (H1.and (hhan.eventually_analyticAt.and hsmall))
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 hhom
  set ρ := min R (min ρ₁ ρ₂) with hρdef
  have hρ : 0 < ρ := lt_min hR (lt_min hρ₁ hρ₂)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρ1 : ρ ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hq : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, μ (b, h (b, s), h (b, s)) = s ∧ AnalyticAt ℂ h (b, s) ∧ ‖h (b, s)‖ < min R (1 / (3 * C)) := by
    intro b hb s hs
    refine hb₁ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hρ1 hb, ball_subset_ball hρ1 hs⟩
  have hhomρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t)) := by
    intro b hb s hs t ht
    refine hb₂ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball hρ2 hb, ball_subset_ball hρ2 hs, ball_subset_ball hρ2 ht⟩
  have hboundρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ :=
    fun b hb s hs t ht => hbound b (ball_subset_ball hρR hb) s (ball_subset_ball hρR hs) t (ball_subset_ball hρR ht)
  have key : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖h (b, s)‖ ^ 2 := by
    intro b hb s hs
    obtain ⟨e1, -, e3⟩ := hq b hb s hs
    have hs' : h (b, s) ∈ ball (0 : Fin g → ℂ) R := by
      rw [mem_ball_zero_iff]; exact e3.trans_le (min_le_left _ _)
    have h1 := hbound b (ball_subset_ball hρR hb) _ hs' _ hs'
    rw [e1] at h1
    have h2 : (2 : ℂ) • h (b, s) - s = -(s - h (b, s) - h (b, s)) := by
      rw [two_smul]; abel
    rw [h2, norm_neg]
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖ := by
    intro b hb s hs
    have h1 := key b hb s hs
    obtain ⟨-, -, e3⟩ := hq b hb s hs
    have h3 : ‖h (b, s)‖ < 1 / (3 * C) := e3.trans_le (min_le_right _ _)
    have h4 : C * ‖h (b, s)‖ ≤ 1 / 3 := by
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    have h5 : ‖(2 : ℂ) • h (b, s)‖ = 2 * ‖h (b, s)‖ := by simp [norm_smul]
    have h6 : ‖(2 : ℂ) • h (b, s)‖ ≤ ‖(2 : ℂ) • h (b, s) - s‖ + ‖s‖ := norm_le_norm_sub_add _ _
    have h7 := norm_nonneg (h (b, s))
    nlinarith
  have hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2 := by
    intro b hb s hs
    refine (key b hb s hs).trans ?_
    have h1 := hcontr b hb s hs
    have h2 : ‖h (b, s)‖ ≤ ‖s‖ := by linarith [norm_nonneg s]
    gcongr
  obtain ⟨L, hLu, hLb⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit b₀ h ρ C hρ hCpos.le hcontr hquad
  have hdiffh : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩
    exact (hq b hb s hs).2.1.differentiableAt.differentiableWithinAt
  have hit := fun k => LocalLog.iter_differentiableOn b₀ h ρ hdiffh hcontr k
  have hDopen : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := isOpen_ball.prod isOpen_ball
  have hLd : DifferentiableOn ℂ L (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hDopen hLu.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun k => by
        show DifferentiableOn ℂ ((2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k) _
        exact (hit k).const_smul _)
  have hLan : AnalyticAt ℂ L (b₀, 0) :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hDopen hLd (b₀, 0)
      (Set.mk_mem_prod (mem_ball_self hρ) (mem_ball_self (x := (0 : Fin g → ℂ)) hρ))
  refine ⟨L, hLan, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds b₀ hρ] with b hb
    have hL0 : L (b, 0) = 0 := by
      have := hLb b hb 0 (mem_ball_self hρ)
      simpa using this
    refine ⟨hL0, ?_⟩
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc' : 0 < c / (4 * C) := by positivity
    filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) (lt_min hρ hc')] with s hs
    have hs1 : s ∈ ball (0 : Fin g → ℂ) ρ := ball_subset_ball (min_le_left _ _) hs
    have hs2 : ‖s‖ < c / (4 * C) := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have h1 := hLb b hb s hs1
    have h2 : 4 * C * ‖s‖ ≤ c := ((lt_div_iff₀' (by positivity)).1 hs2).le
    simp only [hL0, sub_zero, ContinuousLinearMap.id_apply]
    calc ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := h1
      _ = 4 * C * ‖s‖ * ‖s‖ := by ring
      _ ≤ c * ‖s‖ := by gcongr
  · have hpt : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s))) :=
      fun b hb s hs => hLu.tendsto_at ⟨hb, hs⟩
    have hadd := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law b₀ h μ L ρ C hρ hCpos.le hcontr hboundρ hhomρ hpt
    have hμs : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), μ p ∈ ball (0 : Fin g → ℂ) ρ := by
      filter_upwards [hμ.continuousAt (ball_mem_nhds (μ (b₀, 0, 0)) hρ)] with p hp
      simpa [hμ0] using hp
    filter_upwards [ball_mem_nhds ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) hρ, hμs] with p hp hq'
    obtain ⟨b, s, t⟩ := p
    rw [← ball_prod_same, ← ball_prod_same] at hp
    exact hadd b hp.1 s hp.2.1 t hp.2.2 hq'

end GlobalTheory.CompanionTheory.Ar.Flat
end

