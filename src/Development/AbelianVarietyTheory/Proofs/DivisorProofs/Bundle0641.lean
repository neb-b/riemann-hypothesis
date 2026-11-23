module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2Limit
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2Limit

theorem norm_sub_sq_le (a : ℕ → ℂ) (m k : ℕ) :
    ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m *
      ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
  have htel : a m - a (k + m) = ∑ i ∈ Finset.range k, (a (i + m) - a (i + m + 1)) := by
    have := Finset.sum_range_sub' (fun i => a (i + m)) k
    simp only [zero_add] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [add_right_comm]
  have h1 : ‖a m - a (k + m)‖ ≤ ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have hg : ∀ i ∈ Finset.range k, (0:ℝ) < (1/2) ^ (i + m) := fun i _ => by positivity
  have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.range k)
    (fun i => ‖a (i + m) - a (i + m + 1)‖) hg
  have hsg : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ≤ 2 / 2 ^ m := by
    have : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) =
        (1/2) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    have := sum_geometric_two_le k
    have h2m : (0:ℝ) < (1/2) ^ m := by positivity
    calc (1/2:ℝ) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ (1/2) ^ m * 2 :=
          mul_le_mul_of_nonneg_left this h2m.le
      _ = 2 / 2 ^ m := by rw [one_div_pow]; ring
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun i hi => hg i hi) ⟨0, by simp [h]⟩)
  rcases hsum_pos with hpos | hk
  · have h3 : (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 ≤
        (∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m)) *
          ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) := by
      rwa [div_le_iff₀ hpos, mul_comm] at h2
    have h4 : ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) =
        ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [h4] at h3
    have hn : 0 ≤ ∑ i ∈ Finset.range k, (2:ℝ) ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖a m - a (k + m)‖ ^ 2 ≤ (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hsg hn
  · subst hk; simp

theorem tendsto_of_summable (a : ℕ → ℂ)
    (hs : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2)) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ ∀ m, ‖a m - L‖ ^ 2 ≤
      2 / 2 ^ m * ∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2 := by
  set c : ℕ → ℝ := fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hfin : ∀ m k, ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m * ∑' i, c (i + m) := by
    intro m k
    refine (norm_sub_sq_le a m k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Summable.sum_le_tsum _ (fun i _ => hc0 _) ((summable_nat_add_iff m).mpr hs)
  have htail := tendsto_sum_nat_add c
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ m in atTop, 2 * ∑' i, c (i + m) < ε ^ 2 := by
      have := htail.const_mul 2
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hev.exists_forall_of_atTop
    refine ⟨m, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + m := ⟨N - m, by omega⟩
    have h1 := hfin m k
    have h2 : 2 / 2 ^ m * ∑' i, c (i + m) ≤ 2 * ∑' i, c (i + m) := by
      refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun i => hc0 _)
      exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have h3 : dist (a (k + m)) (a m) ^ 2 < ε ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev]; linarith [hm m le_rfl]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun m => ?_⟩
  have hlim : Tendsto (fun k => ‖a m - a (k + m)‖ ^ 2) atTop (𝓝 (‖a m - L‖ ^ 2)) :=
    (((hL.comp (tendsto_add_atTop_nat m)).const_sub (a m)).norm).pow 2
  exact le_of_tendsto' hlim fun k => hfin m k

end GlobalTheory.L2Limit

namespace GlobalTheory.L2Limit

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]


open Classical in
noncomputable def limSec (F : ℕ → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  if ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) then limUnder atTop (fun m => F m i y) else 0

theorem limSec_eq (F : ℕ → ι → Y → ℂ) (i : ι) (y : Y) {c : ℂ}
    (h : Tendsto (fun m => F m i y) atTop (𝓝 c)) : limSec F i y = c := by
  unfold limSec; rw [if_pos ⟨c, h⟩]; exact h.limUnder_eq

theorem limSec_trans (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i j : ι) (y : Y) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : limSec F i y = A.g la i j y * limSec F j y := by
  have hg := A.g_ne la i j y hi hj
  have hseq : (fun m => F m i y) = fun m => A.g la i j y * F m j y :=
    funext fun m => (hF m).2 i j y hi hj
  by_cases hc : ∃ c, Tendsto (fun m => F m j y) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [limSec_eq F j y hc, limSec_eq F i y (by rw [hseq]; exact hc.const_mul _)]
  · have hc' : ¬ ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      apply hc
      refine ⟨(A.g la i j y)⁻¹ * c, ?_⟩
      have h2 : Tendsto (fun m => A.g la i j y * F m j y) atTop (𝓝 c) := by
        rw [← hseq]; exact hc'
      have := h2.const_mul (A.g la i j y)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hg] using this
    unfold limSec
    rw [if_neg hc, if_neg hc', mul_zero]

theorem limSec_aemeas (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i : ι) :
    AEMeasurable (limSec F i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target) := by
  classical
  set T := (A.chart i).target with hTdef
  have hT : MeasurableSet T := (A.chart i).open_target.measurableSet
  let G : ℕ → V n → ℂ := fun m => T.piecewise (F m i ∘ (A.chart i).symm) 0
  have hG : ∀ m, StronglyMeasurable (G m) := fun m =>
    (ContinuousOn.measurable_piecewise ((hF m).1 i).continuousOn continuousOn_const
      hT).stronglyMeasurable
  have hS := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hG
  have hL := StronglyMeasurable.limUnder (l := atTop) hG
  have hmeas : StronglyMeasurable ({v | ∃ c, Tendsto (fun m => G m v) atTop (𝓝 c)}.piecewise
      (fun v => limUnder atTop (fun m => G m v)) (fun _ => (0:ℂ))) :=
    StronglyMeasurable.piecewise hS hL stronglyMeasurable_const
  refine hmeas.measurable.aemeasurable.congr ?_
  refine (ae_restrict_iff' hT).mpr (Eventually.of_forall fun v hv => ?_)
  have hGv : (fun m => G m v) = fun m => F m i ((A.chart i).symm v) :=
    funext fun m => by simp only [G, Set.piecewise_eq_of_mem _ _ _ hv, Function.comp_apply]
  simp only [Set.piecewise, Set.mem_setOf_eq, hGv, Function.comp_apply, limSec]

theorem measurable_step (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (j : ℕ) :
    Measurable (fun y => ENNReal.ofReal (A.nsq la (F j - F (j + 1)) y)) :=
  ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq la (F j - F (j + 1)) (fun i k y hi hk => by
      simp only [Pi.sub_apply]; rw [(hF j).2 i k y hi hk, (hF (j + 1)).2 i k y hi hk]; ring)
    (fun i => ((hF j).1 i).continuousOn.sub ((hF (j + 1)).1 i).continuousOn)).measurable

end

theorem exists_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  intro n Y _ _ _ _ _ ι La _ A la F K hK hF hn
  set L := A.kap + la with hLdef
  set e : ℕ → Y → ℝ≥0∞ := fun j y => ENNReal.ofReal (A.nsq L (F j - F (j + 1)) y) with he_def
  have he : ∀ j, Measurable (e j) := measurable_step A L F hF
  have hint : ∀ j, ∫⁻ y, e j y ∂A.mu ≤ ENNReal.ofReal (K / 4 ^ j) := hn
  set S : ℕ → Y → ℝ≥0∞ := fun m y => ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m =>
    Measurable.tsum fun k => measurable_const.mul (he _)
  have hSint : ∀ m, ∫⁻ y, S m y ∂A.mu ≤ ENNReal.ofReal (K / 2 ^ m * 2) := by
    intro m
    show ∫⁻ y, ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu ≤ _
    rw [lintegral_tsum fun k => ((he (k + m)).const_mul _).aemeasurable]
    calc ∑' k, ∫⁻ y, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu
        = ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ∫⁻ y, e (k + m) y ∂A.mu := by
          congr 1; ext k; exact lintegral_const_mul _ (he _)
      _ ≤ ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ENNReal.ofReal (K / 4 ^ (k + m)) :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hint _
      _ = ∑' k, ENNReal.ofReal (K / 2 ^ m * (1 / 2) ^ k) := by
          congr 1; ext k
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4:ℝ) ^ (k + m) = 2 ^ (k + m) * 2 ^ (k + m) by rw [← mul_pow]; norm_num]
          rw [pow_add, one_div_pow]; field_simp
      _ = ENNReal.ofReal (∑' k, K / 2 ^ m * (1 / 2) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (K / 2 ^ m * 2) := by rw [tsum_mul_left, tsum_geometric_two]
  have hfin : ∀ᵐ y ∂A.mu, S 0 y < ⊤ :=
    ae_lt_top (hSm 0) ((hSint 0).trans_lt ENNReal.ofReal_lt_top).ne
  have hpt : ∀ m, ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ≤
      ENNReal.ofReal (2 / 2 ^ m) * S m y := by
    intro m
    filter_upwards [hfin] with y hy
    set p := A.pick y
    set E := Real.exp (-A.ph L p y) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set a : ℕ → ℂ := fun j => F j p y with ha
    have he_eq : ∀ j, e j y = ENNReal.ofReal (‖a j - a (j + 1)‖ ^ 2 * E) := fun j => rfl
    set b : ℕ → ℝ := fun k => 2 ^ k * (‖a k - a (k + 1)‖ ^ 2 * E) with hb_def
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hSb : ∀ m', S m' y = ∑' k, ENNReal.ofReal (b (k + m')) := by
      intro m'
      simp only [hSdef, he_eq]
      congr 1; ext k
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hb : Summable b := by
      have h0 := hSb 0
      simp only [add_zero] at h0
      have hs := ENNReal.summable_toReal (h0 ▸ hy.ne)
      refine hs.congr fun k => ?_
      exact ENNReal.toReal_ofReal (hb0 k)
    have hb' : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2) := by
      refine (hb.div_const E).congr fun k => ?_
      simp only [hb_def]; field_simp
    obtain ⟨Lm, hLm, hbd⟩ := tendsto_of_summable a hb'
    have hf : limSec F p y = Lm := limSec_eq F p y hLm
    have hnsq : A.nsq L (F m - limSec F) y = ‖a m - Lm‖ ^ 2 * E := by
      show ‖F m p y - limSec F p y‖ ^ 2 * E = _
      rw [hf]
    rw [hnsq, hSb m, ← ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
      ((summable_nat_add_iff m).mpr hb), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbd m) hEpos.le
    calc ‖a m - Lm‖ ^ 2 * E
        ≤ 2 / 2 ^ m * (∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2) * E := this
      _ = 2 / 2 ^ m * ∑' k, b (k + m) := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 2; ext k; simp only [hb_def]; ring
  refine ⟨limSec F, fun i j y hi hj => limSec_trans A L F hF i j y hi hj,
    fun i => limSec_aemeas A L F hF i, fun m => ?_⟩
  calc n0 A la (F m - limSec F) = ∫⁻ y, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ∂A.mu := rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 / 2 ^ m) * S m y ∂A.mu := lintegral_mono_ae (hpt m)
    _ = ENNReal.ofReal (2 / 2 ^ m) * ∫⁻ y, S m y ∂A.mu := lintegral_const_mul _ (hSm m)
    _ ≤ ENNReal.ofReal (2 / 2 ^ m) * ENNReal.ofReal (K / 2 ^ m * 2) := by gcongr; exact hSint m
    _ = ENNReal.ofReal (4 * K / 4 ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (4:ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp; ring

end GlobalTheory.L2Limit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloLimitIncreasingWeights
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem holo_limit_increasing_weights : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (F0 : M → ℂ) (om : M → ℝ) (c : ℝ) (p : ℕ → M → ℝ) (q : M → ℝ) (F : ℕ → M → ℂ) (B : ℝ≥0∞), Continuous F0 → Continuous om → 0 < c → (∀ x, c ≤ om x ∧ om x ≤ 1) → (∀ k, SmoothR n X.z (p k)) → (∀ x, Antitone (fun k => p k x)) → (∀ x, Tendsto (fun k => p k x) atTop (𝓝 (q x))) → (∀ k, Holo n X.z (F k)) → B < ⊤ → (∀ k, ∫⁻ x, ENNReal.ofReal (‖F0 x - F k x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z ≤ B) → ∃ G : M → ℂ, Holo n X.z G ∧ ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))) ∂vol n X.z ≤ B := by
  intro n M _ _ _ _ _ X F0 om c p q Fk B hF0 hom hc hombd hp hpanti hpq hF hBtop hB
  have hz := X.isLocalHomeomorph
  have hpc : ∀ k, Continuous (p k) := fun k => by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ (hp k))
    exact this.congr fun x => by simp
  have hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G := fun G hG =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)
  have hC : ReciprocityTheory.L2DbarEstimates.I.HoloClosedNeed n M :=
    ReciprocityTheory.L2DbarEstimates.F.holoClosedNeed n M (regMAll n M)
  have hE : ReciprocityTheory.L2DbarEstimates.I.EvalNeed n M := ReciprocityTheory.L2DbarEstimates.F.evalNeed n M C.mv
  set Iw : ℕ → (M → ℂ) → ℝ≥0∞ := fun k G =>
    ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z with hIw
  set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-p 0 x)))
    with hμ
  have hkey : ∀ f : M → ℂ, AEStronglyMeasurable f μ →
      wint n X.z f (p 0) = eLpNorm f 2 μ ^ (2 : ℝ) := fun f hf => by
    rw [ReciprocityTheory.L2DbarEstimates.I.fx_wint_eq_withDensity n X.z (p 0) (hpc 0).measurable f,
      ReciprocityTheory.L2DbarEstimates.I.fx_lintegral_enorm_sq_eq,
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf]
    norm_num [hμ]
  have hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G →
      wint n X.z G (p 0) = ENNReal.ofReal (‖v‖ ^ 2) := fun v G h => by
    rw [hkey G ((Lp.stronglyMeasurable v).aestronglyMeasurable.congr h),
      ReciprocityTheory.L2DbarEstimates.I.fx_lp_norm_sq_eq μ v G h]

  have hmono : ∀ G k k', k ≤ k' → Iw k G ≤ Iw k' G := fun G k k' h => by
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.exp (-p k x) ≤ Real.exp (-p k' x) :=
      Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 : 0 ≤ om x := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)

  have hmeas : ∀ G : M → ℂ, Continuous G → ∀ (w : M → ℝ), Continuous w →
      Measurable fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-w x))) :=
    fun G hG w hw => (ENNReal.continuous_ofReal.comp (((hF0.sub hG).norm.pow 2).mul
      (hom.mul (Real.continuous_exp.comp hw.neg)))).measurable

  have hbd : ∀ G : M → ℂ, Continuous G → wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤
      ENNReal.ofReal (2 / c) * (Iw 0 G + Iw 0 (Fk 0)) := fun G hG => by
    rw [hIw, ← lintegral_add_left (hmeas G hG _ (hpc 0)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have ha : 0 ≤ ‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    have hb : 0 ≤ ‖F0 x - Fk 0 x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set s := ‖F0 x - G x‖
    set t := ‖F0 x - Fk 0 x‖
    set e := Real.exp (-p 0 x)
    have he : 0 < e := Real.exp_pos _
    have hu : ‖G x - Fk 0 x‖ ≤ s + t := by
      calc ‖G x - Fk 0 x‖ = ‖(F0 x - Fk 0 x) - (F0 x - G x)‖ := by congr 1; ring
        _ ≤ t + s := norm_sub_le _ _
        _ = s + t := add_comm _ _
    have hu2 : ‖G x - Fk 0 x‖ ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
      have h0 := norm_nonneg (G x - Fk 0 x)
      nlinarith [sq_nonneg (s - t), norm_nonneg (F0 x - G x), norm_nonneg (F0 x - Fk 0 x)]
    have hoc : 1 ≤ om x / c := (one_le_div hc).mpr (hombd x).1
    have hst : 0 ≤ s ^ 2 + t ^ 2 := by positivity
    calc ‖G x - Fk 0 x‖ ^ 2 * e ≤ 2 * (s ^ 2 + t ^ 2) * e := by gcongr
      _ ≤ 2 * (s ^ 2 + t ^ 2) * e * (om x / c) := le_mul_of_one_le_right (by positivity) hoc
      _ = 2 / c * (s ^ 2 * (om x * e) + t ^ 2 * (om x * e)) := by field_simp

  have hIfin : ∀ k, Iw 0 (Fk k) ≤ B := fun k => (hmono (Fk k) 0 k (Nat.zero_le k)).trans (hB k)
  have hfin : ENNReal.ofReal (2 / c) * (B + B) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hBtop, hBtop⟩)
  have hbdB : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B →
      wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤ ENNReal.ofReal (2 / c) * (B + B) :=
    fun G hG h => (hbd G hG).trans (by gcongr; exact hIfin 0)

  have hEv : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ →
      ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ x - G₂ x‖ ≤ C * ‖w‖ := by
    intro x
    obtain ⟨C, hC⟩ := hE X (p 0) x (hp 0)
    refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩
    have h := hC _ (Holo.sub n X.z _ _ h₁ h₂)
    rw [hN w _ hw] at h
    have h' : ENNReal.ofReal (‖G₁ x - G₂ x‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact h.trans (by gcongr; exact le_max_left _ _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (le_max_right _ _)]
    exact h'
  choose Cev hCev0 hCev using hEv
  have hmem : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B → MemLp (fun x => G x - Fk 0 x) 2 μ :=
    fun G hG h => by
    have h1 := ((hkey _ (hG.sub (hcont _ (hF 0))).measurable.aestronglyMeasurable).symm.trans_le
      (hbdB G hG h)).trans_lt hfin
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h1
  let K : ℕ → Set (Lp ℂ 2 μ) := fun k => {v | ∃ G : M → ℂ, Holo n X.z G ∧
    (v : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B}
  have hanti : Antitone K := by
    intro k k' h v hv
    obtain ⟨G, hG, hvG, hI⟩ := hv
    exact ⟨G, hG, hvG, (hmono G k k' h).trans hI⟩
  have hne : ∀ k, (K k).Nonempty := fun k =>
    ⟨(hmem (Fk k) (hcont _ (hF k)) (hIfin k)).toLp _, Fk k, hF k, MemLp.coeFn_toLp _, hB k⟩

  have hclosed : ∀ k, IsClosed (K k) := by
    intro k
    refine IsSeqClosed.isClosed fun vs v hvs hlimv => ?_
    have hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧
        (vs i : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B := hvs
    choose G hG hvG hIG using hvs'
    have hvm : Measurable (v : M → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hF0m : Measurable (Fk 0) := (hcont _ (hF 0)).measurable
    have hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ]
        fun x => G i x - ((v : M → ℂ) x + Fk 0 x) := fun i => by
      filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2
      rw [h1, Pi.sub_apply, h2]; ring
    have hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlimv
    have hw : Tendsto (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0))
        atTop (𝓝 0) := by
      have he : (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0)) =
          fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2) := funext fun i => hN _ _ (hd i)
      rw [he]
      have : Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)
      simpa using this
    obtain ⟨Gl, hGl, hfG⟩ :=
      hC X (p 0) G (fun x => (v : M → ℂ) x + Fk 0 x) (hp 0) hG (hvm.add hF0m) hw
    have hfGμ : (fun x => (v : M → ℂ) x + Fk 0 x) =ᵐ[μ] Gl :=
      (withDensity_absolutelyContinuous _ _).ae_le hfG
    have hvGl : (v : M → ℂ) =ᵐ[μ] fun x => Gl x - Fk 0 x := by
      filter_upwards [hfGμ] with x hx
      rw [← hx]; ring
    have hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x := fun i => by
      filter_upwards [hd i, hfGμ] with x h1 h2
      rw [h1, h2]
    have hpt : ∀ x, Tendsto (fun i => G i x) atTop (𝓝 (Gl x)) := by
      intro x
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun i => norm_nonneg _)
        (fun i => hCev x (G i) Gl (hG i) hGl _ (hd2 i)) ?_
      simpa using hlim0.const_mul (Cev x)
    refine ⟨Gl, hGl, hvGl, ?_⟩
    have hf : ∀ x, Tendsto (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
        (om x * Real.exp (-p k x)))) atTop
        (𝓝 (ENNReal.ofReal (‖F0 x - Gl x‖ ^ 2 * (om x * Real.exp (-p k x))))) := fun x =>
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_const_nhds.sub (hpt x)).norm.pow 2).mul_const _)
    calc Iw k Gl = ∫⁻ x, liminf (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
          (om x * Real.exp (-p k x)))) atTop ∂vol n X.z := by
          refine lintegral_congr fun x => ?_
          exact ((hf x).liminf_eq).symm
      _ ≤ liminf (fun i => Iw k (G i)) atTop :=
          lintegral_liminf_le fun i => hmeas _ (hcont _ (hG i)) _ (hpc k)
      _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hIG)
  have hmid : ∀ k, ∀ v ∈ K k, ∀ w ∈ K k, (2 : ℂ)⁻¹ • (v + w) ∈ K k := by
    rintro k v ⟨G, hG, hvG, hIv⟩ w ⟨G', hG', hwG, hIw'⟩
    refine ⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x),
      Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG]
        with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]; ring
    · have hhalf : ENNReal.ofReal (1 / 2) * (B + B) = B := by
        rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc Iw k (fun x => (2 : ℂ)⁻¹ * (G x + G' x))
          ≤ ENNReal.ofReal (1 / 2) * (Iw k G + Iw k G') := by
            rw [hIw, ← lintegral_add_left (hmeas G (hcont _ hG) _ (hpc k)),
              ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono fun x => ?_
            have h0 : 0 ≤ om x * Real.exp (-p k x) := by
              have := hc.le.trans (hombd x).1; positivity
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by norm_num)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hs : F0 x - (2 : ℂ)⁻¹ * (G x + G' x) =
                (2 : ℂ)⁻¹ * ((F0 x - G x) + (F0 x - G' x)) := by ring
            have hn : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ≤
                (‖F0 x - G x‖ + ‖F0 x - G' x‖) / 2 := by
              rw [hs, norm_mul, norm_inv, Complex.norm_two]
              have := norm_add_le (F0 x - G x) (F0 x - G' x)
              linarith
            have hn2 : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ^ 2 ≤
                (‖F0 x - G x‖ ^ 2 + ‖F0 x - G' x‖ ^ 2) / 2 := by
              have h0' := norm_nonneg (F0 x - (2 : ℂ)⁻¹ * (G x + G' x))
              nlinarith [sq_nonneg (‖F0 x - G x‖ - ‖F0 x - G' x‖),
                mul_le_mul hn hn h0' (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_right hn2 h0]
        _ ≤ ENNReal.ofReal (1 / 2) * (B + B) := by gcongr
        _ = B := hhalf
  have hbdd : Bornology.IsBounded (K 0) := by
    set R := (ENNReal.ofReal (2 / c) * (B + B)).toReal with hRdef
    refine (Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := R + 1)).subset ?_
    rintro v ⟨G, hG, hvG, hI⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (hN v _ hvG).symm.trans_le (hbdB G (hcont _ hG) hI)
    rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne] at h1
    have hR : 0 ≤ R := ENNReal.toReal_nonneg
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  obtain ⟨v, hv⟩ := cvx (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd
  obtain ⟨G, hG, hvG, -⟩ := hv 0
  have hIk : ∀ k, Iw k G ≤ B := fun k => by
    obtain ⟨G', hG', hvG', hI'⟩ := hv k
    have heq : G = G' := funext fun x => by
      have h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x := by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3
        rw [h1, Pi.zero_apply]
        linear_combination h2 - h3
      have h1 := hCev x G G' hG hG' 0 h0
      rw [norm_zero, mul_zero] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    rw [heq]; exact hI'
  refine ⟨G, hG, ?_⟩
  have hmon : ∀ x, Monotone fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) := fun x k k' h => by
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)
  have hlimx : ∀ x, Tendsto (fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x)))) atTop
      (𝓝 (ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))))) := fun x =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((((Real.continuous_exp.tendsto _).comp (hpq x).neg).const_mul _).const_mul _)
  have hT := lintegral_tendsto_of_tendsto_of_monotone
    (μ := vol n X.z) (fun k => (hmeas G (hcont _ hG) _ (hpc k)).aemeasurable)
    (ae_of_all _ hmon) (ae_of_all _ hlimx)
  exact le_of_tendsto' hT hIk

end

end GlobalTheory
end

