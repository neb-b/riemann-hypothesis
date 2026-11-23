module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Vanish
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronValue

theorem lintegral_ball_lt_top {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w g H : V n → ℝ}
    (hd : ContinuousOn d Ω) (hdpos : ∀ z ∈ Ω, 0 < d z)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.closedBall (0 : V n) ρ ⊆ Ω) (hg : ∀ z, 0 ≤ g z)
    (hH : ∀ z ∈ Metric.ball (0 : V n) ρ, H z = g z * w z)
    (hfin : ∫⁻ z, ENNReal.ofReal (H z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z) < ⊤ := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (d z)) (volume.restrict Ω) :=
    (hd.aemeasurable hΩ.measurableSet).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hfin
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V n) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ ((hd.mul hw).mono hB)
  set c := d z0 * w z0 with hc
  have hcpos : 0 < c := mul_pos (hdpos _ (hB hz0)) (hwpos _ (hB hz0))
  have hsub : Metric.ball (0 : V n) ρ ⊆ Ω := Metric.ball_subset_closedBall.trans hB
  calc ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z)
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal c⁻¹ *
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have h1 : c ≤ d z * w z := hmin (Metric.ball_subset_closedBall hz)
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hdpos z (hsub hz)).le, ← ENNReal.ofReal_mul (inv_pos.2 hcpos).le,
          hH z hz]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hcpos]
        nlinarith [mul_le_mul_of_nonneg_right h1 (hg z)]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V n) ρ,
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set hsub).trans_lt hfin)

theorem lintegral_lt_top_of_cutoff {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w S : V n → ℝ}
    {χ F : V n → ℂ} (hd : ContinuousOn d Ω)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {δ : ℝ}
    (hB : Metric.closedBall (0 : V n) δ ⊆ Ω) (hχ : Continuous χ) (hχ0 : ∀ z, δ ≤ ‖z‖ → χ z = 0)
    {M : ℝ} (hM : ∀ z ∈ Ω, S z ≤ M) (hS : ∀ᵐ z ∂(volume.restrict Ω), 0 < S z) {p : ℝ} (hp : 0 ≤ p)
    (hfin : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p))
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤ := by
  set μ := (volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z) with hμ
  have hK := isCompact_closedBall (0 : V n) δ
  have hKm : MeasurableSet (Metric.closedBall (0 : V n) δ) := hK.measurableSet
  have hμK : μ (Metric.closedBall 0 δ) < ⊤ := by
    rw [hμ, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.2 hB]
    exact Integrable.lintegral_lt_top ((hd.mono hB).integrableOn_compact hK)
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn
    (f := fun z => 2 * (‖χ z‖ ^ 2 * w z))
    (continuousOn_const.mul ((hχ.norm.pow 2).continuousOn.mul (hw.mono hB)))
  have hac : μ ≪ volume.restrict Ω := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂μ, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ≤
      (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z +
        ENNReal.ofReal (2 * M ^ p) * ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p)) := by
    filter_upwards [hac.ae_le hS, hac.ae_le (ae_restrict_mem hΩ.measurableSet)] with z hz hzΩ
    have hz : 0 < S z := hz
    have hzΩ : z ∈ Ω := hzΩ
    have hMpos : 0 < M := hz.trans_le (hM z hzΩ)
    have hwz := hwpos z hzΩ
    have h1 : ENNReal.ofReal (2 * (‖χ z‖ ^ 2 * w z)) ≤
        (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z := by
      by_cases hzK : z ∈ Metric.closedBall (0 : V n) δ
      · rw [Set.indicator_of_mem hzK]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hBd z hzK))
      · have : δ ≤ ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hzK; exact hzK.le
        simp [hχ0 z this]
    have h2 : 1 ≤ M ^ p * S z ^ (-p) := by
      rw [Real.rpow_neg hz.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hz p)]
      exact Real.rpow_le_rpow hz.le (hM z hzΩ) hp
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖χ z‖ ^ 2 + 2 * ‖χ z - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖χ z‖ + ‖χ z - F z‖ := by
        simpa using norm_sub_le (χ z) (χ z - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg (χ z), norm_nonneg (χ z - F z),
        sq_nonneg (‖χ z‖ - ‖χ z - F z‖)]
    have hA : 0 ≤ ‖χ z - F z‖ ^ 2 * w z := by positivity
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine le_trans ?_ (add_le_add_left h1 _)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (mul_nonneg hA (Real.rpow_nonneg hz.le _)))).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hwz.le, mul_le_mul_of_nonneg_right h2 hA]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hKm), lintegral_indicator_const hKm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_eq {r : ℕ} (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm L P x = ‖P x‖ * X.nfac L x := rfl

theorem value_and_integrability : (VanishAtSStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) := by
  intro hV r X la L w0 s ψ x0 bb ε δ χ F hn ho hw0 hs hψ hψC hbb hε hB hχ hχ1 hχ0 hF hfin hw0x hsx hdet
  have hΩ := OntoB.isOpen_OmF X x0
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := IW.zero_mem_OmF X x0 ho
  have hcpt : Continuous (cpt X x0) := (OntoB.cd_cpt X x0).continuous
  set w : V (nd X) → ℝ := fun z =>
    Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hwdef
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  have hwpos : ∀ z ∈ OmF X x0, 0 < w z := fun z _ => div_pos (Real.exp_pos _) (hka z)
  have hw : ContinuousOn w (OmF X x0) := by
    have h1 := OntoE.expPhla_cont X x0 la
    have h2 : ContinuousOn (fun z => Real.exp (-ψ (cpt X x0 z))) (OmF X x0) :=
      Real.continuous_exp.comp_continuousOn (hψ.comp hcpt.continuousOn fun _ hz => hz).neg
    have h3 : ContinuousOn (kaF X x0 bb) (OmF X x0) := fun z hz =>
      (OntoB.ka_contDiffAt bb hz).continuousAt.continuousWithinAt
    refine ((h1.mul h2).div h3 fun z _ => (hka z).ne').congr fun z _ => ?_
    simp only [hwdef, Pi.div_apply, Pi.mul_apply]
    rw [← Real.exp_add, neg_add]
  have hfin' : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ := by
    simpa only [hwdef, mul_div_assoc] using hfin
  have hS : ∀ z, ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) * X.nfac L (cpt X x0 z) ^ 2 := fun z => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pnorm_eq, mul_pow]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (hs k).1.1
  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ∂muF X x0 < ⊤ := by
    choose C hC using fun k => (hs k).2
    refine lintegral_lt_top_of_cutoff hΩ OntoB.densF_continuousOn hw hwpos hB hχ hχ0
      (M := ∑ k, C k ^ 2) (fun z hz => Finset.sum_le_sum fun k _ => ?_) ?_ (Nat.cast_nonneg _) hfin'
    · have hp : 0 ≤ X.pnorm L (s k) (cpt X x0 z) := by
        rw [pnorm_eq]; exact mul_nonneg (norm_nonneg _) (OntoE.nfac_pos X x0 hz).le
      exact pow_le_pow_left₀ hp (hC k _ hz) 2
    · obtain ⟨k, hk⟩ := HE.coord_ne_of_det hn hdet
      have hne : ∃ z ∈ OmF X x0, s k (cpt X x0 z) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hk
        filter_upwards [hΩ.mem_nhds h0] with z hz
        simp [hall z hz]
      have hnull := OntoD.null_zero hΩ (OmFConnStatement_holds r X x0 ho) (hsd k) hne
      rw [ae_restrict_iff' hΩ.measurableSet]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzΩ
      have hsk : s k (cpt X x0 z) ≠ 0 := fun h => hz ⟨hzΩ, h⟩
      rw [hS]
      refine mul_pos ?_ (pow_pos (OntoE.nfac_pos X x0 hzΩ) 2)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hsk) 2⟩
  have haeΩ : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Δ, zOf, bOf, -, -, -, -, -, hLU⟩ := lu_holds r X x0 ho
    have hz : ∀ z ∈ OmF X x0, zOf (cpt X x0 z) = z := fun z hz => by
      have := (hLU z hz _ (ExtFPf.oneF_mem X)).2.1
      rwa [ExtFPf.rmul_oneF] at this
    obtain ⟨ρ0, hρ0, hρB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds h0)
    set ρ := min ρ0 ε
    have hρ : 0 < ρ := lt_min hρ0 hε
    have hcB : Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x0 :=
      (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hρB
    have hbB : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x0 := Metric.ball_subset_closedBall.trans hcB
    have key := hV r X x0 hn ho (IW.orth_mem_dom X x0 ho) (fun y => 1 - F (zOf y)) w0 s ρ hρ
      (((differentiableOn_const (1 : ℂ)).sub (hF.mono hbB)).congr fun z hz' => by
        simp [hz z (hbB hz')])
      (fun k => (hsd k).mono hbB) ((OntoB.hol_comp X x0 hw0.1.1).mono hbB) hw0x hsx hdet ?_
    · have h00 : zOf x0 = 0 := by simpa [IW.cpt_zero] using hz 0 h0
      simp only [h00] at key
      exact (sub_eq_zero.1 key).symm
    · refine lintegral_ball_lt_top hΩ OntoB.densF_continuousOn (fun z => OntoB.densF_pos)
        (w := fun z => w z * (X.nfac L (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ?_ ?_ hρ hcB ?_ ?_ hfin'
      · exact hw.mul (((OntoE.nfac_cont X x0 L).pow 2).rpow_const fun z hz' =>
          Or.inl (pow_pos (OntoE.nfac_pos X x0 hz') 2).ne')
      · exact fun z hz' => mul_pos (hwpos z hz')
          (Real.rpow_pos_of_pos (pow_pos (OntoE.nfac_pos X x0 hz') 2) _)
      · intro z; positivity
      · intro z hz'
        have : ‖z‖ ≤ ε := (mem_ball_zero_iff.1 hz').le.trans (min_le_right _ _)
        rw [hS, Real.mul_rpow (by positivity) (by positivity), hχ1 z this, hz z (hbB hz')]
        ring
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hmain
    filter_upwards [haeΩ] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le)]
    congr 1
    simp only [hwdef]; ring
  · intro C _ _
    obtain ⟨A, hA⟩ := hψC
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt ?_
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun z => ENNReal.ofReal (Real.exp A) *
      ENNReal.ofReal (‖F z‖ ^ 2 * w z)) ?_) ?_
    · filter_upwards [haeΩ] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [hwdef, kaF]
      rw [← Real.exp_sub, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hA _ hz, mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmain

end GlobalTheory.KronValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrderToIntegral

open Filter Metric

theorem norm_le_of_det {n : ℕ} {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0)
    (hdet : f'.det ≠ 0) (h0 : f 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in 𝓝 (0 : V n), ‖z‖ ≤ K * ‖f z‖ := by
  obtain ⟨K, hKpos, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (HE.ker_bot_of_det hdet)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK' : ∀ z : V n, ‖z‖ ≤ K * ‖f' z‖ := fun z => by
    have := hK.le_mul_dist z 0
    simpa using this
  have hlo := hf.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hlo] with z hz
  rw [h0, sub_zero, sub_zero] at hz
  have h1 : ‖f' z‖ ≤ ‖f z‖ + 1 / (2 * K) * ‖z‖ := by
    have : ‖f' z‖ ≤ ‖f z‖ + ‖f z - f' z‖ := by
      calc ‖f' z‖ = ‖f z - (f z - f' z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have h2 : (K : ℝ) * (1 / (2 * K) * ‖z‖) = ‖z‖ / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hK0.le
  have h4 := hK' z
  rw [mul_add, h2] at h3
  linarith

theorem sum_sq_lower {n : ℕ} (hn : 0 < n) {w : V n → ℂ} {s : Fin n → V n → ℂ}
    (hw : ContinuousAt w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ ∑ k, ‖s k z‖ ^ 2 := by
  have hF : DifferentiableAt ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0 := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    apply hdet
    show LinearMap.det (0 : V n →ₗ[ℂ] V n) = 0
    rw [LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin, zero_pow (by omega)]
  obtain ⟨K, hK, hle⟩ := norm_le_of_det hF.hasFDerivAt hdet (by ext k; simp [hs0])
  have hpos : 0 < ‖w 0‖ := norm_pos_iff.2 hw0
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖w 0‖ / 2 ≤ ‖w z‖ :=
    (hw.norm.tendsto.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun z hz => le_of_lt hz
  refine ⟨(‖w 0‖ / 2) ^ 2 / K ^ 2, by positivity, ?_⟩
  filter_upwards [hle, hg] with z hz hwz
  have hwz0 : 0 < ‖w z‖ := lt_of_lt_of_le (half_pos hpos) hwz
  have e1 : ‖(WithLp.toLp 2 fun k => s k z / w z : V n)‖ ^ 2 = (∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    simp [div_pow]
  have h1 : ‖z‖ ^ 2 ≤ K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2) := by
    rw [← e1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : (‖w 0‖ / 2) ^ 2 ≤ ‖w z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwz 2
  calc (‖w 0‖ / 2) ^ 2 / K ^ 2 * ‖z‖ ^ 2
      ≤ ‖w z‖ ^ 2 / K ^ 2 * (K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2)) := by gcongr
    _ = ∑ k, ‖s k z‖ ^ 2 := by field_simp

theorem lintegral_lt_top {n : ℕ} (hn : 0 < n) {g : V n → ℂ} {S : V n → ℝ} {a : ℕ} {c : ℝ}
    (hc : 0 < c) (hS : ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ S z)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hC, hO⟩ := hg.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hO.bound.and hS)
  have : Nontrivial (V n) := ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, by
    intro h
    have h1 := congrArg (fun v : V n => v ⟨0, hn⟩) h
    simp at h1⟩⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with he
  have he0 : 0 ≤ e := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hint := (mvInt n hn ((n : ℝ) - 1 / 2)).2 (by linarith)
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  have hfin : ENNReal.ofReal (C ^ 2 * c ^ (-e)) *
      ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * ((n : ℝ) - 1 / 2)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (lintegral_mono_set (ball_subset_ball (min_le_right ε 1)))
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : V n) (min ε 1))), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : V n)))
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  obtain ⟨h1, h2⟩ := hball z (ball_subset_ball (min_le_left ε 1) hz)
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [ENNReal.ofReal_rpow_of_pos hz, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_pow, norm_norm] at h1
  have h3 : ‖g z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : S z ^ (-e) ≤ (c * ‖z‖ ^ 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have hSz : 0 ≤ S z := le_trans (by positivity) h2
  have h5 : (‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e) = ‖z‖ ^ (-2 * ((n : ℝ) - 1 / 2)) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hz.le,
      ← Real.rpow_add hz]
    congr 1
    rw [he]
    push_cast
    ring
  calc ‖g z‖ ^ 2 * S z ^ (-e) ≤ (C * ‖z‖ ^ a) ^ 2 * (c * ‖z‖ ^ 2) ^ (-e) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hSz _) (by positivity)
    _ = C ^ 2 * c ^ (-e) * ((‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e)) := by
        rw [Real.mul_rpow hc.le (by positivity)]
        ring
    _ = _ := by rw [h5]

end GlobalTheory.OrderToIntegral

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanS_of_isBigO : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ)
    (g : Frame X.Ψ r → ℂ), ContinuousOn g X.dom →
    (∀ j, (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
    VanS X Fl.xs Fl.s a g := by
  intro r X Xa Fl a g _ hO j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hw0 : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 :=
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
      rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]⟩
  have hw : ContinuousAt (fun z : V (nd X) => Fl.w0 (cpt X (Fl.xs j) z)) 0 := by
    refine ContinuousAt.comp (g := Fl.w0) ?_ (FundSetPf.cont_cpt X (Fl.xs j)).continuousAt
    rw [IW.cpt_zero]
    exact hw0.1.continuousOn.continuousAt ((FourierCoefficientDomain.isOpen_dom X).mem_nhds (Fl.xs_mem j))
  obtain ⟨c, hc, hS⟩ := OrderToIntegral.sum_sq_lower
    (w := fun z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) hn hw
    (by simpa only [IW.cpt_zero] using Fl.w0_ne j) (by simpa only [IW.cpt_zero] using hs0)
    (Fl.coord j)
  exact OrderToIntegral.lintegral_lt_top hn hc hS (hO j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.VanishOfSimpleZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.VanishAtSimpleZero

open Filter Metric

theorem lintegral_eq_top {n : ℕ} (hn : 0 < n) {g S : V n → ℝ} {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hρ : 0 < ρ) (hg : ∀ᶠ z in 𝓝 (0 : V n), a ≤ g z)
    (hS : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < S z ∧ S z ≤ c * ‖z‖ ^ 2) :
    ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) = ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.and hS)
  have hr0 : 0 < min ε ρ := lt_min hε hρ
  have hsubε : ball (0 : V n) (min ε ρ) ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball (0 : V n) (min ε ρ) ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinf : ∫⁻ z in ball (0 : V n) (min ε ρ), ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) = ⊤ := by
    have hδ : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
    have hT := ReciprocityTheory.L2DbarEstimates.I.vanish_div n hn ReciprocityTheory.L2DbarEstimates.C.mvDiv hr0 hc hδ
    refine top_unique (le_of_tendsto' hT fun k => ?_)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz _ => ?_))
    have hpos : 0 < c * ‖z‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hz) 2)
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_)
    · have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · simp
  have hlow : ENNReal.ofReal a * ∫⁻ z in ball (0 : V n) (min ε ρ),
      ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) ≤
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsubρ)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz hzb => ?_))
    obtain ⟨hgz, hSz⟩ := hball z (hsubε hzb)
    obtain ⟨hS0, hSle⟩ := hSz hz
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hgz (Real.rpow_le_rpow_of_nonpos hS0 hSle (by simp))
      (Real.rpow_nonneg (by positivity) _) (ha.le.trans hgz))
  rw [hinf, ENNReal.mul_top (by simpa using ha)] at hlow
  exact top_unique hlow

theorem vanish_of_simple_zero {n : ℕ} (hn : 0 < n) {u w : V n → ℂ} {s : Fin n → V n → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ContinuousAt u 0) (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hw : DifferentiableAt ℂ w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0)
    (hint : ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-(n : ℝ))) < ⊤) : u 0 = 0 := by
  by_contra hu0
  set f : V n → V n := fun z => (WithLp.toLp 2 fun k => s k z / w z : V n) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.iso_zero hfd.hasFDerivAt hdet hf0
  have hSpos : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < ∑ k, ‖s k z‖ ^ 2 := by
    filter_upwards [closedBall_mem_nhds (0 : V n) hδ] with z hz hz0
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (Ne.symm fun hsum => hz0 ?_)
    refine hiso z hz ?_
    have hk : ∀ k, s k z = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hsum k (Finset.mem_univ _)
      simpa using this
    ext k
    simp [hf, hk k]
  have hbig : ∀ k, ∃ C > 0, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    obtain ⟨C, hC, hCw⟩ := ((hs k).hasFDerivAt.isBigO_sub).exists_pos
    refine ⟨C, hC, hCw.bound.mono fun z hz => ?_⟩
    simpa [hs0 k] using hz
  choose C hC hCb using hbig
  have hSle : ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ (∑ k, C k ^ 2 + 1) * ‖z‖ ^ 2 := by
    filter_upwards [Filter.eventually_all.2 hCb] with z hz
    calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
      _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; simp [mul_pow]
      _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]
  have hpos : 0 < ‖u 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
  have hcont : ContinuousAt (fun z => ‖u z‖ ^ 2) 0 := hu.norm.pow 2
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖u 0‖ ^ 2 / 2 ≤ ‖u z‖ ^ 2 :=
    hcont.eventually (le_mem_nhds (show ‖u 0‖ ^ 2 / 2 < ‖u 0‖ ^ 2 by linarith))
  have htop := lintegral_eq_top hn (g := fun z => ‖u z‖ ^ 2) (S := fun z => ∑ k, ‖s k z‖ ^ 2)
    (by positivity) (by positivity : (0 : ℝ) < ∑ k, C k ^ 2 + 1) hρ hg
    (by filter_upwards [hSpos, hSle] with z h1 h2 hz0 using ⟨h1 hz0, h2⟩)
  exact absurd hint (by rw [htop]; exact lt_irrefl _)

end GlobalTheory.VanishAtSimpleZero

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hdu hds hdw hw0 hs0 hdet hint
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1
  have hb : Metric.ball (0 : V (nd X)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have key := VanishAtSimpleZero.vanish_of_simple_zero hn (u := fun z => u (cpt X x1 z))
    (w := fun z => w0 (cpt X x1 z)) (s := fun k z => s k (cpt X x1 z)) hρ
    ((hdu.differentiableAt hb).continuousAt) (fun k => (hds k).differentiableAt hb)
    (hdw.differentiableAt hb) (by simpa [h0] using hw0) (fun k => by simpa [h0] using hs0 k) hdet hint
  simpa [h0] using key

end GlobalTheory
end

