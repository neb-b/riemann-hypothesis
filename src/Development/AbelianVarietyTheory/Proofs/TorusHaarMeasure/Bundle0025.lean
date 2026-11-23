module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeDensity
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PointSup

theorem point_le {p k K e c : ℝ} {w S : ℝ≥0∞} (hk : 0 < k) (hkK : k ≤ K) (hc : 0 < c) (hce : c ≤ e)
    (hw : w ≠ 0) (hS : (ENNReal.ofReal e / w) ^ (1 / 2 : ℝ) ≤ S)
    (hfin : ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ < ⊤) :
    ENNReal.ofReal p ≤
      ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by
  rcases le_or_gt p 0 with hp | hp
  · simp [ENNReal.ofReal_of_nonpos hp]
  have hK : 0 < K := hk.trans_le hkK
  have hwt : w ≠ ⊤ := by
    rintro rfl
    have h1 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
    have h2 : ENNReal.ofReal k⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hk)).ne'
    rw [ENNReal.mul_top h1, ENNReal.top_mul h2] at hfin
    exact lt_irrefl _ hfin

  have hS2 : ENNReal.ofReal e / w ≤ S ^ 2 := by
    have h := ENNReal.pow_le_pow_left (n := 2) hS
    have h' : ((ENNReal.ofReal e / w) ^ (1 / 2 : ℝ)) ^ 2 = ENNReal.ofReal e / w := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rwa [h'] at h
  have he : ENNReal.ofReal e ≤ S ^ 2 * w := (ENNReal.div_le_iff hw hwt).1 hS2
  have hreal : 1 ≤ k⁻¹ * (K / c) * e := by
    have h1 : 1 ≤ K / k := by rw [le_div_iff₀ hk]; linarith
    have h2 : 1 ≤ e / c := by rw [le_div_iff₀ hc]; linarith
    have h3 : k⁻¹ * (K / c) * e = (K / k) * (e / c) := by simp only [div_eq_mul_inv]; ring
    rw [h3]; nlinarith

  have hone : 1 ≤ w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (k⁻¹ * (K / c) * e) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal k⁻¹ * ENNReal.ofReal (K / c) * ENNReal.ofReal e := by
          rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hk.le) (div_nonneg hK.le hc.le)),
            ENNReal.ofReal_mul (inv_nonneg.2 hk.le)]
      _ ≤ ENNReal.ofReal k⁻¹ * ENNReal.ofReal (K / c) * (S ^ 2 * w) := by gcongr
      _ = w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by ring
  calc ENNReal.ofReal p = ENNReal.ofReal p * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal p * (w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2)) := by gcongr
    _ = _ := by ring

theorem mean_le {n : ℕ} {R : ℝ} {u : V n → ℂ} (hu : DifferentiableOn ℂ u (Metric.ball 0 R))
    {g : V n → ℝ≥0∞} (hg : Measurable g) {J A : ℝ≥0∞} (hJ : J < ⊤)
    (hgJ : ∫⁻ z in Metric.ball (0 : V n) R, g z ≤ J)
    (hpt : ∀ z ∈ Metric.ball (0 : V n) R, g z < ⊤ → ENNReal.ofReal (‖u z‖ ^ 2) ≤ g z * A) :
    ENNReal.ofReal ‖u 0‖ ^ 2 * volume (Metric.ball (0 : V n) R) ≤ J * A := by
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n 0 R u (fun _ => 1) hu measurable_const
  simp only [mul_one, setLIntegral_one] at hmv

  have hfin : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : V n) R)), g z < ⊤ :=
    ae_lt_top hg (hgJ.trans_lt hJ).ne
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : V n) R)), ‖u z‖ₑ ^ 2 ≤ g z * A := by
    filter_upwards [hfin, ae_restrict_mem measurableSet_ball] with z hz hzb
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact hpt z hzb hz
  calc ENNReal.ofReal ‖u 0‖ ^ 2 * volume (Metric.ball (0 : V n) R)
      = ‖u 0‖ₑ ^ 2 * volume (Metric.ball (0 : V n) R) := by rw [ofReal_norm]
    _ ≤ ∫⁻ z in Metric.ball (0 : V n) R, ‖u z‖ₑ ^ 2 := hmv
    _ ≤ ∫⁻ z in Metric.ball (0 : V n) R, g z * A := lintegral_mono_ae hae
    _ = (∫⁻ z in Metric.ball (0 : V n) R, g z) * A := lintegral_mul_const A hg
    _ ≤ J * A := by gcongr

theorem lintegral_le_density {n : ℕ} {B O : Set (V n)} (hB : MeasurableSet B) (hBO : B ⊆ O)
    {d : V n → ℝ} {c : ℝ} (hc : 0 < c) (hd : ∀ z ∈ B, c ≤ d z) (g : V n → ℝ≥0∞) :
    ∫⁻ z in B, g z ≤ (ENNReal.ofReal c)⁻¹ *
      ∫⁻ z, g z ∂((volume.restrict O).withDensity fun z => ENNReal.ofReal (d z)) := by

  have hμ : ENNReal.ofReal c • volume.restrict B ≤
      (volume.restrict O).withDensity fun z => ENNReal.ofReal (d z) := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, withDensity_apply _ hs,
      Measure.restrict_restrict hs, smul_eq_mul]
    calc ENNReal.ofReal c * volume (s ∩ B) = ∫⁻ _ in s ∩ B, ENNReal.ofReal c :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in s ∩ B, ENNReal.ofReal (d z) :=
          setLIntegral_mono' (hs.inter hB) fun z hz => ENNReal.ofReal_le_ofReal (hd z hz.2)
      _ ≤ ∫⁻ z in s ∩ O, ENNReal.ofReal (d z) :=
          lintegral_mono_set (Set.inter_subset_inter_right s hBO)
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  calc ∫⁻ z in B, g z = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ z in B, g z) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    _ = (ENNReal.ofReal c)⁻¹ * ∫⁻ z, g z ∂(ENNReal.ofReal c • volume.restrict B) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by gcongr

theorem root_le {a S J v : ℝ≥0∞} {K k : ℝ} (hJ : J < ⊤) (hv : v ≠ 0) (hvt : v ≠ ⊤) (hK : 0 ≤ K)
    (hk : 0 ≤ k) (h : a ^ 2 * v ≤ J * (ENNReal.ofReal (K * k) * S ^ 2)) :
    a ≤ ENNReal.ofReal (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) * S := by
  have hJv : J / v ≠ ⊤ := ENNReal.div_ne_top hJ.ne hv
  have ht0 : 0 ≤ (J / v).toReal := ENNReal.toReal_nonneg
  have h1 : a ^ 2 ≤ J / v * (ENNReal.ofReal (K * k) * S ^ 2) := by
    rw [← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hv) (Or.inl hvt)]
    exact h
  have e1 : (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) ^ 2 = (J / v).toReal * (K * k) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ht0 hK), Real.sq_sqrt hk]; ring
  have h2 : a ^ 2 ≤ (ENNReal.ofReal (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) * S) ^ 2 := by
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), e1, ENNReal.ofReal_mul ht0,
      ENNReal.ofReal_toReal hJv, mul_assoc]
    exact h1
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pointSup : (MeasInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ c ≤ densF X x z ∧ densF X x z ≤ C ∧ c ≤ X.nfac la (cpt X x z) ∧ X.nfac la (cpt X x z) ≤ C) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) := by
  intro hMI hU _ r X x0 hx0 la W bb κ hκ hW hWL F P hIn hP hPF ρ hρ _
  obtain ⟨hκm, hκpos, hκB, hκka, -, ρ1, C1, hρ1, hκloc⟩ := hκ
  obtain ⟨ρ0, c0, C0, hρ0, hc0, hU0⟩ := hU r X la
  obtain ⟨cw, hcw, hWl⟩ := hWL

  obtain ⟨φ, hφ⟩ : ∃ φ : Frame X.Ψ r → ℝ≥0∞,
      φ = fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul (ENNReal.measurable_ofReal.comp hκm.inv)
  have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y := by
    intro y hy b hb
    rw [hφ]
    simp only
    rw [OntoE.phiF_B X hP.2 hW y hy b hb, hκB y hy b hb]
  have hφdom : ∀ y ∈ X.dom, φ y = ENNReal.ofReal (‖P y‖ ^ 2) * W y * ENNReal.ofReal (κ y)⁻¹ := by
    intro y hy
    rw [hφ]
    simp only
    rw [OntoE.phiF_dom X P W hy]
  have hφout : ∀ y, y ∉ X.dom → φ y = 0 := by
    intro y hy
    rw [hφ]
    simp [OntoE.phiF, Set.piecewise, hy]

  have hI : ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hIn
    by_cases hz : cpt X x0 z ∈ X.dom
    · rw [hφdom _ hz, hPF z hz, hκka z hz, div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
      exact le_of_eq (by ring)
    · rw [hφout _ hz]
      exact zero_le
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min ρ (min ρ0 ρ1) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; exact lt_min hρ (lt_min hρ0 hρ1)
  have hball : ∀ z ∈ Metric.ball (0 : V (nd X)) R, ‖z‖ < ρ ∧ ‖z‖ < ρ0 ∧ ‖z‖ < ρ1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [hR] at hz
    exact ⟨hz.trans_le (min_le_left _ _), hz.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = (ENNReal.ofReal c0)⁻¹ * ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 :=
    ⟨_, rfl⟩
  have hJfin : J < ⊤ := by
    rw [hJ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hc0)) hI
  have hv : volume (Metric.ball (0 : V (nd X)) R) ≠ 0 := (Metric.measure_ball_pos volume _ hRpos).ne'
  have hvt : volume (Metric.ball (0 : V (nd X)) R) ≠ ⊤ := measure_ball_lt_top.ne
  have hK0 : 0 ≤ max C1 0 / c0 ^ 2 := div_nonneg (le_max_right _ _) (sq_nonneg _)
  refine ⟨Real.sqrt ((J / volume (Metric.ball (0 : V (nd X)) R)).toReal * (max C1 0 / c0 ^ 2)),
    fun x hx => ?_⟩
  have hxd : x ∈ X.dom := IW.orth_mem_dom X x hx
  have hκx : 0 < κ x := (hκpos x hxd).1
  have hcd : Differentiable ℂ (fun z : V (nd X) => cpt X x z) := by
    rw [differentiable_pi]; intro τ
    rw [differentiable_pi]; intro a
    rw [differentiable_pi]; intro b
    exact (IW.cpt_entry_cd X x τ a b).differentiable (by simp)
  have hmaps : ∀ z ∈ Metric.ball (0 : V (nd X)) R, cpt X x z ∈ X.dom :=
    fun z hz => (hU0 x hx z (hball z hz).2.1).1
  have hu : DifferentiableOn ℂ (fun z => P (cpt X x z)) (Metric.ball (0 : V (nd X)) R) :=
    hP.1.comp hcd.differentiableOn hmaps
  have hg : Measurable fun z => φ (cpt X x z) := hφm.comp hcd.continuous.measurable

  have hgJ : ∫⁻ z in Metric.ball (0 : V (nd X)) R, φ (cpt X x z) ≤ J := by
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) R, φ (cpt X x z)
        ≤ (ENNReal.ofReal c0)⁻¹ * ∫⁻ z, φ (cpt X x z) ∂muF X x :=
          lintegral_le_density (O := OmF X x) (d := densF X x) measurableSet_ball hmaps hc0
            (fun z hz => (hU0 x hx z (hball z hz).2.1).2.1) _
      _ = J := by rw [hJ, hMI r X x0 x hx0 hx φ hφm hφB]
  have key : ∀ S : ℝ≥0∞, (∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom →
      (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) ≤ S) →
      ENNReal.ofReal ‖P x‖ ≤
        ENNReal.ofReal (Real.sqrt ((J / volume (Metric.ball (0 : V (nd X)) R)).toReal *
          (max C1 0 / c0 ^ 2)) * Real.sqrt (κ x)) * S := by
    intro S hSle
    have hpt : ∀ z ∈ Metric.ball (0 : V (nd X)) R, φ (cpt X x z) < ⊤ →
        ENNReal.ofReal (‖P (cpt X x z)‖ ^ 2) ≤
          φ (cpt X x z) * (ENNReal.ofReal (max C1 0 / c0 ^ 2 * κ x) * S ^ 2) := by
      intro z hz hfin
      obtain ⟨hzρ, hzρ0, hzρ1⟩ := hball z hz
      obtain ⟨hyd, -, -, hn1, -⟩ := hU0 x hx z hzρ0
      have hky : 0 < κ (cpt X x z) := (hκpos _ hyd).1
      have hkK : κ (cpt X x z) ≤ max C1 0 * κ x :=
        (hκloc x hx z hzρ1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hκx.le)
      have hce : c0 ^ 2 ≤ Real.exp (-phla X la (cpt X x z)) := by
        have hn : 0 < X.nfac la (cpt X x z) := hc0.trans_le hn1
        have h2 : Real.exp (-phla X la (cpt X x z)) = X.nfac la (cpt X x z) ^ 2 := by
          show Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) = _
          rw [neg_mul, neg_neg, two_mul, Real.exp_add, Real.exp_log hn]; ring
        rw [h2]; nlinarith
      have hw : W (cpt X x z) ≠ 0 :=
        (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (mul_pos hcw (Real.exp_pos _))) (hWl _ hyd)).ne'
      rw [hφdom _ hyd] at hfin ⊢
      have h := point_le hky hkK (pow_pos hc0 2) hce hw (hSle z hzρ hyd) hfin
      rwa [show max C1 0 * κ x / c0 ^ 2 = max C1 0 / c0 ^ 2 * κ x by ring] at h
    have hmean := mean_le hu hg hJfin hgJ hpt
    simp only [IW.cpt_zero] at hmean
    exact root_le hJfin hv hvt hK0 hκx.le hmean
  exact key _ fun z hz hd => le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd le_rfl))

end GlobalTheory.PointSup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
section
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspDecay

end CuspDecay

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma isUStab_one' {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin r → E)) : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (1 : GL (Fin r) E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma lact_one_eq_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_div_la1_nonneg {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ 1 / X.la1 x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact one_div_nonneg.mpr (Real.sqrt_nonneg _)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_div_mul_le_one_div_of_ratio_bounds {k c m0 m1 : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hp : 0 < 1 / (c * m0)) (h1 : m0 ≤ k * m1) (h2 : m1 ≤ k * m0) :
    1 / k * (1 / (c * m0)) ≤ 1 / (c * m1) := by
  have hp' : 0 < c * m0 := one_div_pos.mp hp
  have hm0 : 0 < m0 := by
    by_contra h
    push_neg at h
    nlinarith
  have hm1 : 0 < m1 := by nlinarith
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (mul_pos hc hm1)
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mul_iInf_le_iInf_of_mul_le {ι : Type*} [Finite ι] {f g : ι → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i, k * g i ≤ f i) : k * ⨅ i, g i ≤ ⨅ i, f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp [Real.iInf_of_isEmpty]
  | inr _ =>
    exact le_ciInf fun i =>
      (mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range g).bddBelow i) hk).trans (h i)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_add_one_div_sqrt_le_two_mul {s0 s1 k : ℝ} (hk : 0 < k) (hk2 : k ≤ 2) (hs0 : 0 ≤ s0)
    (h1 : s0 ≤ k * s1) (h2 : s1 ≤ k * s0) : 1 + 1 / √s1 ≤ 2 * (1 + 1 / √s0) := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    have hs1 : s1 ≤ 0 := by simpa using h2
    simp [Real.sqrt_eq_zero'.mpr hs1]
  · have hs1 : 0 < s1 := by nlinarith
    have hu := Real.sqrt_pos.mpr h
    have hv := Real.sqrt_pos.mpr hs1
    have h4 : s0 ≤ 4 * s1 := by nlinarith
    have hle : √s0 ≤ 2 * √s1 := by
      rw [show (2 : ℝ) * √s1 = √(4 * s1) by
        rw [Real.sqrt_mul' _ hs1.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h4
    have h3 : 1 / √s1 ≤ 2 / √s0 := by
      rw [div_le_div_iff₀ hv hu]
      linarith
    have h5 : 2 / √s0 = 2 * (1 / √s0) := by ring
    have h6 : 0 ≤ 1 / √s0 := by positivity
    linarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exp_half_le_of_comparable_lemma_4 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ)
    {a θ C A' : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hps : ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 1 ≤ X.tt ξ x τ) →
      ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * ((1 - θ) / 4)) * a * ⨅ τ, X.tt ξ x τ)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (htt : ∀ τ, 2 ≤ X.tt ξ x τ)
    (hcmp : ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + (1 - θ) / 2) * X.maj y τ v ∧
      X.maj y τ v ≤ (1 + (1 - θ) / 2) * X.maj x τ v) :
    Real.exp (ps y / 2) ≤ Real.exp ((C + |A'| * Real.log 2) / 2) *
      (1 + 1 / X.la1 x) ^ (|A'| / 2) * Real.exp (-4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) := by
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have htty : ∀ τ, 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ ≤ X.tt ξ y τ := by
    intro τ
    have hpos := htt τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt] at hpos ⊢
    exact one_div_mul_le_one_div_of_ratio_bounds (by linarith only [hθ1]) (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ) (by linarith only [hpos])
      (hcmp τ _).1 (hcmp τ _).2
  have hty1 : ∀ τ, 1 ≤ X.tt ξ y τ := by
    intro τ
    have h1 := htty τ
    have h2 := htt τ
    have h3 : 1 ≤ 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith only [hθ1])]
      linarith only [h2, hθ0]
    linarith only [h1, h3]
  have hTy : 1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ ≤ ⨅ τ, X.tt ξ y τ :=
    mul_iInf_le_iInf_of_mul_le (by positivity) htty
  have hsq := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + (1 - θ) / 2)) (k2 := 1 + (1 - θ) / 2)
    (by positivity) (by linarith only [hθ1])
    (fun τ w => by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])]
      linarith only [(hcmp τ w).1])
    (fun τ w => (hcmp τ w).2)
  have hL : 1 + 1 / X.la1 y ≤ 2 * (1 + 1 / X.la1 x) := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    refine one_add_one_div_sqrt_le_two_mul (k := 1 + (1 - θ) / 2) (by linarith only [hθ1]) (by linarith only [hθ0])
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx) ?_ hsq.2
    have h := hsq.1
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])] at h
    linarith only [h]
  have hly0 : 0 ≤ 1 / X.la1 y := one_div_la1_nonneg X y
  have hLy0 : 0 ≤ Real.log (1 + 1 / X.la1 y) := Real.log_nonneg (le_add_of_nonneg_right hly0)
  have hLyle : Real.log (1 + 1 / X.la1 y) ≤ Real.log 2 + Real.log (1 + 1 / X.la1 x) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hla0]))]
    exact Real.log_le_log (by linarith only [hly0]) hL
  have hpsy := hps y hy ξ hξ hty1
  have hA : A' * Real.log (1 + 1 / X.la1 y) ≤
      |A'| * (Real.log 2 + Real.log (1 + 1 / X.la1 x)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A') hLy0).trans
      (mul_le_mul_of_nonneg_left hLyle (abs_nonneg _))
  have hθε : θ * (1 + (1 - θ) / 2) ≤ 1 - 2 * ((1 - θ) / 4) := by nlinarith [sq_nonneg (θ - 1)]
  have hkey : θ * ⨅ τ, X.tt ξ x τ ≤ (1 - 2 * ((1 - θ) / 4)) * ⨅ τ, X.tt ξ y τ := by
    have h1 : θ * ⨅ τ, X.tt ξ x τ ≤
        (1 - 2 * ((1 - θ) / 4)) * (1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hT0
      rw [mul_one_div, le_div_iff₀ (by linarith only [hθ1])]
      exact hθε
    exact h1.trans (mul_le_mul_of_nonneg_left hTy (by linarith only [hθ0]))
  have hexp : ps y / 2 ≤ (C + |A'| * Real.log 2) / 2 +
      Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ := by
    have h8 := mul_le_mul_of_nonneg_left hkey (by positivity : 0 ≤ 8 * Real.pi * a)
    linarith only [hpsy, hA, h8]
  calc Real.exp (ps y / 2)
      ≤ Real.exp ((C + |A'| * Real.log 2) / 2 +
          Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) :=
        Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by linarith only [hla0])]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.pnorm_le_exp_neg_tt_near_cusp :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ∧ X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ) (a : ℝ), X.IsSec la F → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cfwM X ps a → 0 ≤ a → (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (X.pnorm la F x) ≤ ENNReal.ofReal C * ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom), ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) / 2))) → ∀ θ a' : ℝ, 0 < θ → θ < 1 → a' = θ * a → ∃ C A : ℝ, 0 ≤ A ∧ ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 2 ≤ X.tt ξ x τ) → X.pnorm la F x ≤ C * (1 + 1 / X.la1 x) ^ A * Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
  intro hcpt hinv hstat r X la F ps a hsec hcf ha hbound θ a' hθ0 hθ1 ha'
  obtain ⟨-, -, hpinv⟩ := hstat
  obtain ⟨ρ, hρ0, hρ1, hnear⟩ := hcpt r X ((1 - θ) / 2) (by linarith)
  obtain ⟨C₀, hC₀⟩ := hbound ρ hρ0 hρ1
  obtain ⟨C, A', hps⟩ := hcf.2 ((1 - θ) / 4) (by linarith) (by linarith)
  refine ⟨max C₀ 0 * Real.exp ((C + |A'| * Real.log 2) / 2), |A'| / 2, by positivity, ?_⟩
  intro x hx ξ hξ htt
  have hb : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  obtain ⟨hx₀, hmaj₀⟩ := hinv r X 1 (isUStab_one' _ _) x hx _ hb
  have hpn := hpinv r X la F hsec 1 (one_mem _) x hx _ hb
  rw [lact_one_eq_self] at hx₀ hmaj₀ hpn
  have horth : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) = x₀ at hx₀ hmaj₀ hpn horth
  have hmaj : ∀ τ v, X.maj x₀ τ v = X.maj x τ v := by
    intro τ v
    simpa using hmaj₀ τ v
  have htt₀ : ∀ τ, X.tt ξ x₀ τ = X.tt ξ x τ := by
    intro τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt, hmaj]
  have hla : X.la1 x₀ = X.la1 x := by
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hx₀ (k1 := 1) (k2 := 1) zero_le_one one_pos
      (fun τ w => by rw [hmaj, one_mul]) (fun τ w => by rw [hmaj, one_mul])
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    exact congrArg Real.sqrt (by linarith [h.1, h.2])
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have hsup : ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z ∈ X.dom),
      ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z) / 2)) ≤
        ENNReal.ofReal (Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
          Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun _ => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hy, hcmp⟩ := hnear x₀ horth z hz
    have h := exp_half_le_of_comparable_lemma_4 X ps ha hθ0 hθ1 hps hx₀ hy hξ
      (fun τ => by rw [htt₀]; exact htt τ) hcmp
    rwa [hla, ← ha', iInf_congr htt₀] at h
  have hB0 : 0 ≤ Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
      Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith only [hla0]) _))
      (Real.exp_pos _).le
  have hfin := (hC₀ x₀ hx₀ horth).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0)) hsup)
  rw [← ENNReal.ofReal_mul (le_max_right _ _), hpn,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_max_right _ _) hB0)] at hfin
  calc X.pnorm la F x ≤ _ := hfin
    _ = _ := by ring

end GlobalTheory
end

