module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.LeOfEventuallyDown
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def QInv (nu : Measure V) (ε δ : ℝ) : Prop :=
  ∀ X : V, ‖X‖ < δ → ∀ r, 0 < r → r < δ →
    nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) ∧
      nu (closedBall 0 r) ≤ nu (closedBall X ((1 + ε) * r))

theorem tendsto_mul_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact mul_pos ht hr

variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

private theorem frequently_filterAt_of_eventually_closedBall (μ : Measure V) [SFinite μ] (x : V) {P : Set V → Prop}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (closedBall x r)) :
    ∃ᶠ a in (Besicovitch.vitaliFamily μ).filterAt x, P a := by
  intro hne
  have h2 := (Besicovitch.tendsto_filterAt μ x).eventually hne
  obtain ⟨r, hr1, hr2⟩ := (h.and h2).exists
  exact hr2 hr1

theorem le_of_eventually_up {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have ha : 0 < 1 - ε := by linarith
  have key : nu s ≤ (M' • lam) s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily nu) (M' • lam)
      MeasureTheory.Measure.AbsolutelyContinuous.rfl s fun x hx => frequently_filterAt_of_eventually_closedBall nu x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr ha)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 - ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 - ε)⁻¹ * ρ := mul_pos (inv_pos.mpr ha) h3
    have hq' := (hq x hx' _ hr h2).1
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x ha.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc nu (closedBall x ρ) ≤ nu (closedBall 0 ((1 - ε)⁻¹ * ρ)) := hq'
      _ ≤ M * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) := h1
      _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) :=
          by gcongr
      _ = M' * lam (closedBall x ρ) := by rw [e, mul_assoc]
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using key

theorem le_of_eventually_down {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have hb : 0 < 1 + ε := by linarith
  have key : ((M' : ℝ≥0∞) • lam) s ≤ nu s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily lam) nu
      (Measure.smul_absolutelyContinuous) s fun x hx => frequently_filterAt_of_eventually_closedBall lam x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr hb)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 + ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 + ε)⁻¹ * ρ := mul_pos (inv_pos.mpr hb) h3
    have hq' := (hq x hx' _ hr h2).2
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x hb.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at e
    simp only [Measure.smul_apply, smul_eq_mul]
    calc (M' : ℝ≥0∞) * lam (closedBall x ρ)
        = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by
          rw [e, mul_assoc]
      _ ≤ M * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by gcongr
      _ ≤ nu (closedBall 0 ((1 + ε)⁻¹ * ρ)) := h1
      _ ≤ nu (closedBall x ρ) := hq'
  simpa only [Measure.smul_apply, smul_eq_mul] using key

theorem tendsto_ofReal_pow (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun ε : ℝ => (1 + σ * ε) ^ n) (𝓝 0) (𝓝 ((1 + σ * 0) ^ n)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).pow n)
  rw [mul_zero, add_zero, one_pow] at h
  have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h
  rw [ENNReal.ofReal_one] at h2
  exact h2.mono_left nhdsWithin_le_nhds

theorem limsup_liminf_bounds {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := Besicovitch.ae_tendsto_rnDeriv nu lam
  have hfin := Measure.rnDeriv_lt_top nu lam
  have hpos : lam (ball (0 : V) δ) ≠ 0 := (measure_ball_pos lam 0 hδ).ne'
  obtain ⟨X, hX, hXt, hXf⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    apply hpos
    have h3 := ae_iff.mp (hae.and hfin)
    refine measure_mono_null (fun y hy => ?_) h3
    show ¬ _
    exact fun h => hcon ⟨y, hy, h.1, h.2⟩
  have hXn : ‖X‖ < δ := mem_ball_zero_iff.mp hX
  have key : ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r →
      nu (closedBall X (t * r)) / lam (closedBall 0 r) =
        ENNReal.ofReal (t ^ finrank ℝ V) * (nu (closedBall X (t * r)) / lam (closedBall X (t * r))) := by
    intro t ht r hr
    rw [Measure.addHaar_closedBall_mul lam X ht.le hr.le, ← mul_div_assoc, ENNReal.mul_div_mul_left]
    · exact (ENNReal.ofReal_pos.mpr (pow_pos ht _)).ne'
    · exact ENNReal.ofReal_ne_top
  have hup : Tendsto (fun r => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hlo : Tendsto (fun r => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r h0 h1
    exact ⟨h0, h1⟩
  refine ⟨nu.rnDeriv lam X, hXf.ne, ?_, ?_⟩
  · refine (Filter.limsup_le_limsup ?_).trans hup.limsup_eq.le
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · refine hlo.liminf_eq.ge.trans (Filter.liminf_le_liminf ?_)
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _

theorem exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  have hlam0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 :=
    fun r hr => (Metric.measure_closedBall_pos lam 0 hr).ne'
  have hlamT : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ :=
    fun r => (isCompact_closedBall (0 : V) r).measure_lt_top.ne
  have hcmp : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    intro ε h0 h1
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    obtain ⟨L, -, hls, hli⟩ := limsup_liminf_bounds lam nu h0 h1 hδ hqδ
    calc ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))
        ≤ ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by gcongr
  have hls_le : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    have A := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inl one_ne_zero) (b := limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    have B := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inl one_ne_zero) (b := liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    rw [one_mul] at A B
    refine le_of_tendsto_of_tendsto A B ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε h0 h1
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring, show (1 : ℝ) + 1 * ε = 1 + ε by ring]
    exact hcmp ε h0 h1
  have heq : liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) = limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := le_antisymm Filter.liminf_le_limsup hls_le
  have hlsT : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ⊤ := by
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, hls, -⟩ := limsup_liminf_bounds lam nu (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hδ hqδ
    exact lt_of_le_of_lt hls (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL).lt_top
  have hup : ∀ C : ℝ≥0, limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C * ENNReal.ofReal ((1 + -1 * ε) ^ finrank ℝ V)) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (lt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu h1 hqδ _ C hMe.le ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (C * ENNReal.ofReal ((1 + 1 * ε) ^ finrank ℝ V) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (gt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [one_mul] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_lt_liminf hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu h0 hqδ _ C hMe.ge ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hc0 : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≠ 0 := by
    intro hzero
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hB : closedBall (0 : V) (δ / 2) ⊆ ball 0 δ := closedBall_subset_ball (by linarith)
    obtain ⟨C, hC0, hClt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (hlamT (δ / 2)) (hpos (δ / 2) (by linarith)).ne'
    have hMe : ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) =
        C * ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hzero, hMe]
      exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hC0.ne')
        (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    have hle := le_of_eventually_up lam nu (by norm_num : (1 / 2 : ℝ) < 1) hqδ _ C hMe.le (by
      filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
      exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le) _ hB
    exact absurd hle (not_le.mpr hClt)
  refine ⟨limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)), hc0, hlsT.ne, hup, fun C hC => hdown C ?_⟩
  rw [heq]
  exact hC

end Formalism.BasicNotions.Examples₂.CD
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.RelDetCore
section
open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

section Core

variable {E : Type*} [Field E] [NumberField E] {N : ℕ}

def detIdeal (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ v : Fin N → Fin N → E, (∀ j, v j ∈ L) ∧ x = (Matrix.of v).det}

theorem of_mulVec_eq (γ : Matrix (Fin N) (Fin N) E) (v : Fin N → Fin N → E) :
    Matrix.of (fun j => γ.mulVec (v j)) = Matrix.of v * γ.transpose := by
  ext i k
  change (∑ l, γ k l * v i l) = ∑ l, v i l * γ k l
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

private theorem det_mem_detIdeal_lemma (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → Fin N → E)
    (hv : ∀ j, v j ∈ L) : (Matrix.of v).det ∈ detIdeal L := by
  unfold detIdeal
  exact Submodule.subset_span ⟨v, hv, rfl⟩

theorem detIdeal_smul (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∀ n ∈ detIdeal L, γ.det • n ∈ detIdeal L := by
  have hle : detIdeal L ≤ (detIdeal L).comap (LinearMap.mulLeft (𝓞 E) γ.det) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have h := det_mem_detIdeal_lemma L (fun j => γ.mulVec (v j)) (fun j => hγ _ (hv j))
    rwa [of_mulVec_eq, Matrix.det_mul, Matrix.det_transpose, mul_comm] at h
  intro n hn
  have h := hle hn
  rwa [Submodule.mem_comap, LinearMap.mulLeft_apply, ← smul_eq_mul] at h

theorem detIdeal_ne_bot (L : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) : detIdeal L ≠ ⊥ := by
  classical
  obtain ⟨b, hbL, hbspan, hbli⟩ : ∃ b ⊆ (L : Set (Fin N → E)),
      Submodule.span E b = Submodule.span E (L : Set (Fin N → E)) ∧
        LinearIndependent E ((↑) : b → Fin N → E) := by
    exact exists_linearIndependent E _
  rw [hsp] at hbspan
  let B : Module.Basis b E (Fin N → E) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  have : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : b ≃ Fin N := Fintype.equivFinOfCardEq hcard
  let v : Fin N → Fin N → E := fun j => ((e.symm j : b) : Fin N → E)
  have hvL : ∀ j, v j ∈ L := fun j => hbL (e.symm j).2
  have hli : LinearIndependent E (fun j => Matrix.of v j) := hbli.comp e.symm e.symm.injective
  have hdet : (Matrix.of v).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  rw [Submodule.ne_bot_iff]
  exact ⟨(Matrix.of v).det, det_mem_detIdeal_lemma L v hvL, hdet⟩

theorem detIdeal_fg (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) : (detIdeal L).FG := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    (S.biUnion fun s => Finset.univ.image s)
  have hL : ∀ x ∈ L, ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (a : 𝓞 E) • x j := by
    have hle : L ≤ ⨅ j : Fin N, (1 : Submodule (𝓞 E) E).comap
        ((a : 𝓞 E) • (LinearMap.proj j : (Fin N → E) →ₗ[𝓞 E] E)) := by
      rw [← hS, Submodule.span_le]
      intro s hs
      simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.proj_apply, Submodule.mem_one]
      intro j
      exact RingHom.mem_rangeS.mp (ha _ (Finset.mem_biUnion.mpr
        ⟨s, hs, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩))
    intro x hx j
    have h := hle hx
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
      LinearMap.proj_apply, Submodule.mem_one] at h
    exact h j
  have hgen : ∀ v : Fin N → Fin N → E, (∀ j, v j ∈ L) →
      ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = ((a : 𝓞 E) ^ N) • (Matrix.of v).det := by
    intro v hv
    choose y hy using fun i j => hL (v i) (hv i) j
    have h1 : (algebraMap (𝓞 E) E (a : 𝓞 E)) • Matrix.of v
        = (algebraMap (𝓞 E) E).mapMatrix (Matrix.of y) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Matrix.of_apply, hy, Algebra.smul_def]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at h2
    exact ⟨(Matrix.of y).det, by rw [← h2, Algebra.smul_def, map_pow]⟩
  have hle : detIdeal L ≤ (1 : Submodule (𝓞 E) E).comap
      (((a : 𝓞 E) ^ N) • (LinearMap.id : E →ₗ[𝓞 E] E)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_one]
    exact hgen v hv
  have hfrac : IsFractional (nonZeroDivisors (𝓞 E)) (detIdeal L) := by
    refine ⟨(a : 𝓞 E) ^ N, pow_mem a.2 N, fun b hb => ?_⟩
    have h := hle hb
    rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_one] at h
    exact RingHom.mem_rangeS.mpr h
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨detIdeal L, hfrac⟩

theorem isIntegral_det_of_stab (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : IsIntegral ℤ γ.det := by
  have h : IsIntegral (𝓞 E) γ.det :=
    isIntegral_of_smul_mem_submodule (detIdeal L) (detIdeal_ne_bot L hsp) (detIdeal_fg L hfg)
      γ.det (detIdeal_smul γ L hγ)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem det_root_of_unity_of_stab [StarRing E]
    (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (hu : γ.det ∈ unitary E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∃ n : ℕ, 0 < n ∧ γ.det ^ n = 1 := by
  have hint_r := isIntegral_det_of_stab γ L hfg hsp hγ
  have hnorm : ∀ φ : E →+* ℂ, ‖φ γ.det‖ = 1 := by
    intro φ
    have h1 : star γ.det * γ.det = 1 := hu.1
    have h2 : starRingEnd ℂ (φ γ.det) * φ γ.det = 1 := by
      rw [← hstar, ← map_mul, h1, map_one]
    have h4 : Complex.normSq (φ γ.det) = 1 := by
      have h := Complex.normSq_eq_conj_mul_self (z := φ γ.det)
      rw [h2] at h
      exact_mod_cast h
    have h5 : ‖φ γ.det‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h4
    nlinarith [norm_nonneg (φ γ.det)]
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := E) (A := ℂ) hint_r hnorm
  exact ⟨n, hn, h⟩

end Core

end Formalism.BasicNotions.Examples₂
end
end

