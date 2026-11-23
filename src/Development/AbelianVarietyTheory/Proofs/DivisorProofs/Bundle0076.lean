module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvLeOfSupportCompact
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem lintegral_inv_le_of_support_compact : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : H)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hC0 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hLc : IsCompact (C * K⁻¹) := hCc.mul hK.inv
  have hLt : μ (C * K⁻¹) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpre : ∀ y : H, μ ((· * y) ⁻¹' C) = (Measure.modularCharacterFun y : ENNReal) * μ C := by
    intro y
    rw [← Measure.map_apply (measurable_mul_const y) hCm,
      Measure.map_right_mul_eq_modularCharacterFun_smul μ y]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hbound : ∀ y ∈ K, Measure.modularCharacterFun y ≤ (μ (C * K⁻¹)).toNNReal / (μ C).toNNReal := by
    intro y hy
    have hsub : (· * y) ⁻¹' C ⊆ (C * K⁻¹) := by
      intro z hz
      exact ⟨z * y, hz, y⁻¹, by simpa using hy, by simp⟩
    have h1 : (Measure.modularCharacterFun y : ENNReal) * μ C ≤ μ (C * K⁻¹) := (hpre y) ▸ measure_mono hsub
    have hCpos : 0 < (μ C).toNNReal := ENNReal.toNNReal_pos hC0 hCt
    rw [le_div_iff₀ hCpos]
    have := ENNReal.toNNReal_mono hLt h1
    simpa [ENNReal.toNNReal_mul] using this
  refine ⟨(μ (C * K⁻¹)).toNNReal / (μ C).toNNReal, fun φ hφ hsupp => ?_⟩
  have key : ∫⁻ x, φ x ∂μ = ∫⁻ x, (Measure.modularCharacterFun x : ENNReal) * φ x⁻¹ ∂μ := by
    have h := measure_mul_lintegral_eq μ μ hCm φ hφ
    simp_rw [hpre, mul_comm _ (μ C), mul_assoc] at h
    rw [lintegral_const_mul' _ _ hCt] at h
    exact (ENNReal.mul_right_inj hC0 hCt).1 h
  rw [key, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x⁻¹ ∈ K
  · have hb := hbound _ hx
    have hmul : (Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x = 1 := by
      rw [← ENNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel,
        Measure.modularCharacterFun_map_one, ENNReal.coe_one]
    calc φ x⁻¹ = ((Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x) * φ x⁻¹ := by rw [hmul, one_mul]
      _ = (Measure.modularCharacterFun x⁻¹ : ENNReal) * ((Measure.modularCharacterFun x : ENNReal) * φ x⁻¹) := by ring
      _ ≤ _ := by gcongr
  · rw [hsupp _ hx]; exact bot_le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormPowMulLeSqrtWeightedSq
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_norm_pow_mul_le_sqrt_weighted_sq :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  intro E F _ _ _ _ _ μ _ _
  set s : ℕ := finrank ℝ E + 1 with hs
  have hfin : ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ < ∞ := by
    apply finite_integral_one_add_norm
    rw [hs]; push_cast
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  set A := ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ with hA
  set B : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * s - 1)) with hB
  refine ⟨A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  intro H hH k
  let f : E → ℝ≥0∞ := fun z => ENNReal.ofReal (((1 + ‖z‖) ^ s)⁻¹)
  let g : E → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖))
  have hf : AEMeasurable f μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    exact ((measurable_const.add measurable_norm).pow_const s).inv
  have hg : AEMeasurable g μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have h1 : ∀ z, (f * g) z = ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) := by
    intro z
    have hp : 0 < (1 + ‖z‖) ^ s := by positivity
    simp only [Pi.mul_apply, f, g]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have h2 : ∀ z, f z ^ (2 : ℝ) = ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) := by
    intro z
    simp only [f]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, inv_pow, ← pow_mul,
      mul_comm]
  have h3 : ∀ z, g z ^ (2 : ℝ) ≤ B * (ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) +
      ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2)) := by
    intro z
    simp only [g, hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := add_pow_le (zero_le_one) (norm_nonneg z) (2 * s)
    rw [Real.rpow_two, add_assoc, ← hs]
    calc ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖)) ^ 2
        = (1 + ‖z‖) ^ (2 * s) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by ring
      _ ≤ (2 ^ (2 * s - 1) * (1 ^ (2 * s) + ‖z‖ ^ (2 * s))) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by
        gcongr
      _ = _ := by rw [one_pow]; ring
  simp only [h1, h2] at key
  refine key.trans ?_
  rw [← hA, mul_assoc, ← ENNReal.mul_rpow_of_nonneg B _ (by norm_num)]
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
  have hm : Measurable fun z : E => ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  rw [← lintegral_add_left hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSublevelTailLeOfFinite
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_sublevel_tail_le (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  have hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1} := fun T =>
    measurableSet_le hx measurable_const
  haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne
  have hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1}) := by
    intro a b hab y hy
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ.withDensity g)
    (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - x y)
    exact ⟨n, by linarith⟩
  rw [hem, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds hε)).exists
  refine ⟨n, fun T hT => ?_⟩
  rw [← withDensity_apply _ (hms T)]
  refine le_trans (measure_mono ?_) hn
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitBallRayAverageLe
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem rayAvg_inner {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ)
    (hΨ : Measurable Ψ) (hd : finrank ℝ E = m + 1) {t : ℝ} (ht : 0 < t) :
    ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ y, (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ := by
  set f : E → ℝ≥0∞ := fun y => if ‖y‖ ≤ t then ENNReal.ofReal (t ^ m * (‖y‖ / t) ^ (m + 1)) * Ψ y else 0
    with hfdef
  have hf : Measurable f := by
    refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hΨ
  have h1 : ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ v, f (t • v) ∂μ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    congr 1; ext v
    have hiff : t * ‖v‖ ≤ t ↔ ‖v‖ ≤ 1 := mul_le_iff_le_one_right ht
    have hdiv : t * ‖v‖ / t = ‖v‖ := by field_simp
    simp only [indicator, Metric.mem_closedBall, dist_zero_right, hfdef, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hiff, hdiv]
  rw [h1, ← lintegral_map hf (measurable_const_smul t), Measure.map_addHaar_smul μ ht.ne',
    lintegral_smul_measure, hd, smul_eq_mul, ← lintegral_const_mul _ hf]
  congr 1; ext y
  simp only [hfdef]
  split_ifs with hy
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    rw [abs_of_pos (inv_pos.mpr (pow_pos ht _))]
    have htne := ht.ne'
    rw [div_pow]
    field_simp
    ring
  · simp

theorem rayAvg_radial (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0; simp
  set g : ℝ → ℝ := fun t => r ^ (m + 1) / t ^ (m + 2) with hgdef
  have hrpow : ∀ t : ℝ, 0 < t → (t ^ (-(m:ℝ) - 2)) = (t ^ (m + 2))⁻¹ := by
    intro t ht
    rw [show (-(m:ℝ) - 2) = -(((m + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
      Real.rpow_natCast]
  have hcongr : EqOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) g (Ioi r) := by
    intro t ht
    simp only [hgdef, hrpow t (hpos.trans ht), div_eq_mul_inv]
  have hint : IntegrableOn g (Ioi r) :=
    (show IntegrableOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) (Ioi r) volume from
      (integrableOn_Ioi_rpow_of_lt (a := -(m:ℝ) - 2)
        (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos).const_mul (r ^ (m + 1))).congr_fun
      hcongr measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := hpos.trans ht
    simp only [Pi.zero_apply, hgdef]; positivity
  have hval : ∫ t in Ioi r, g t = 1 / ((m:ℝ) + 1) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos]
    rw [show (-(m:ℝ) - 2 + 1) = -(((m + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    have : 0 < r ^ (m + 1) := pow_pos hpos _
    field_simp
    push_cast; ring
  have hgm : Measurable fun t : ℝ => ENNReal.ofReal (g t) :=
    ENNReal.measurable_ofReal.comp (by simp only [hgdef]; fun_prop)
  calc ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t * a := by
        refine le_trans (setLIntegral_le_lintegral _ _) (le_of_eq ?_)
        congr 1; ext t
        simp only [indicator, mem_Ici, hgdef]
        split_ifs <;> simp
    _ = (∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t) * a :=
        lintegral_mul_const _ (hgm.indicator measurableSet_Ici)
    _ = (∫⁻ t in Ioi r, ENNReal.ofReal (g t)) * a := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

theorem rayAvg_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  intro E _ _ _ _ _ μ _ Ψ m hΨ hd
  have hF : Measurable fun p : E × ℝ => ENNReal.ofReal (p.2 ^ m * ‖p.1‖ ^ (m + 1)) * Ψ (p.2 • p.1) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp (measurable_snd.smul measurable_fst))
  have hK : Measurable fun p : ℝ × E =>
      (if ‖p.2‖ ≤ p.1 then ENNReal.ofReal (‖p.2‖ ^ (m + 1) / p.1 ^ (m + 2)) * Ψ p.2 else 0) := by
    refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_fst) ?_
      measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp measurable_snd)
  calc ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ
      = ∫⁻ t in Ioi (0:ℝ), (∫⁻ v in Metric.closedBall (0:E) 1,
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ t in Ioi (0:ℝ), (∫⁻ y,
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ) :=
        setLIntegral_congr_fun measurableSet_Ioi (fun t ht => rayAvg_inner μ Ψ m hΨ hd ht)
    _ = ∫⁻ y, (∫⁻ t in Ioi (0:ℝ),
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0)) ∂μ :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 / ((m : ℝ) + 1)) * Ψ y ∂μ :=
        lintegral_mono (fun y => rayAvg_radial m (norm_nonneg y) (Ψ y))
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := lintegral_const_mul _ hΨ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
section
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

variable (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]

noncomputable def toNorm : integralClosure S L →+* integralClosure D (TensorProduct S D L) :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).toRingHom.comp
      (integralClosure S L).val.toRingHom)
    (integralClosure D (TensorProduct S D L)) (fun o => by
      have h : IsIntegral S (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L) (o : L)) :=
        o.2.map _
      exact h.tower_top)

@[simp] theorem toNorm_coe (o : integralClosure S L) :
    ((toNorm S L D o : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) =
      (1 : D) ⊗ₜ[S] (o : L) := rfl

variable {S L D}

noncomputable def locHom (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime] :
    Localization.AtPrime (Q.comap (toNorm S L D)) →+* Localization.AtPrime Q :=
  IsLocalization.lift (M := (Q.comap (toNorm S L D)).primeCompl)
    (g := (algebraMap _ (Localization.AtPrime Q)).comp (toNorm S L D)) (fun s =>
      IsLocalization.map_units (Localization.AtPrime Q) (⟨toNorm S L D s, s.2⟩ : Q.primeCompl))

theorem locHom_algebraMap (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime]
    (o : integralClosure S L) :
    locHom Q (algebraMap _ _ o) = algebraMap _ (Localization.AtPrime Q) (toNorm S L D o) :=
  IsLocalization.lift_eq _ _

end GlobalTheory.AbhyankarLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorAtAugmentationCounitalComul
section
open scoped TensorProduct

namespace GlobalTheory

theorem localFactor_counital_descends :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  intro k A _ _ _ _ ε Δ ⟨hL, hR⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set I : Ideal A := RingHom.ker ε with hI
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun m => OrderDual.toDual (I ^ m), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)
  have hst : ∀ m, n ≤ m → I ^ n = I ^ m := fun m hm => hn m hm
  set N := n + 1 with hN
  set J : Ideal A := I ^ N with hJ
  have hJJ : IsIdempotentElem J := by
    show J * J = J
    rw [hJ, ← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨e', he', hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg J hfg).mp hJJ
  have he'J : e' ∈ J := by rw [hJe]; exact Submodule.mem_span_singleton_self e'
  have hJI : J ≤ I := Ideal.pow_le_self (by omega)
  have he'0 : ε e' = 0 := hJI he'J
  refine ⟨1 - e', by simp [he'0], he'.one_sub, ?_⟩
  have hspan : Ideal.span {1 - (1 - e')} = J := by
    rw [sub_sub_cancel, hJe]
  rw [hspan]
  set mk : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J with hmk
  let ε' : A ⧸ J →ₐ[k] k := Ideal.Quotient.liftₐ J ε (fun a ha => hJI ha)
  have hε' : ∀ a, ε' (mk a) = ε a := fun a => rfl
  have hnil : ∀ y ∈ RingHom.ker ε', IsNilpotent y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J y
    have ha : a ∈ I := by rw [RingHom.mem_ker] at hy ⊢; rw [← hε']; exact hy
    refine ⟨N, ?_⟩
    rw [← map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow ha N)
  let φ : (A ⧸ J) ⊗[k] (A ⧸ J) →ₐ[k] k := Algebra.TensorProduct.productMap ε' ε'
  let Δ'' : A →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := (Algebra.TensorProduct.map mk mk).comp Δ
  have hφ : ∀ t : A ⊗[k] A, φ (Algebra.TensorProduct.map mk mk t)
      = ε (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, hε', mul_comm]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hφΔ : ∀ a, φ (Δ'' a) = ε a := by
    intro a
    show φ (Algebra.TensorProduct.map mk mk (Δ a)) = ε a
    rw [hφ, hR]
  let iL : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeLeft
  let iR : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeRight
  have key : ∀ t : (A ⧸ J) ⊗[k] (A ⧸ J), t - algebraMap k _ (φ t) ∈ nilradical _ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      set u := x - algebraMap k (A ⧸ J) (ε' x) with hu
      set v := y - algebraMap k (A ⧸ J) (ε' y) with hv
      have hu0 : IsNilpotent u := hnil _ (by simp [RingHom.mem_ker, u])
      have hv0 : IsNilpotent v := hnil _ (by simp [RingHom.mem_ker, v])
      have hL : iL u ∈ nilradical _ :=
        mem_nilradical.2 (hu0.map _)
      have hR' : iR v ∈ nilradical _ :=
        mem_nilradical.2 (hv0.map _)
      have heq : x ⊗ₜ[k] y - algebraMap k _ (φ (x ⊗ₜ[k] y)) =
          iL u * iR v
          + algebraMap k _ (ε' y) * iL u
          + algebraMap k _ (ε' x) * iR v := by
        have h1 : x ⊗ₜ[k] y = iL x * iR y := by
          simp [iL, iR, Algebra.TensorProduct.tmul_mul_tmul]
        have h2 : iL x = iL u + algebraMap k _ (ε' x) := by
          rw [← AlgHom.commutes iL, ← map_add (f := _)]; simp [u]
        have h3 : iR y = iR v + algebraMap k _ (ε' y) := by
          rw [← AlgHom.commutes iR, ← map_add (f := _)]; simp [v]
        have h4 : φ (x ⊗ₜ[k] y) = ε' x * ε' y := by simp [φ]
        rw [h4, map_mul, h1, h2, h3]; ring
      rw [heq]
      exact add_mem (add_mem (Ideal.mul_mem_right _ _ hL) (Ideal.mul_mem_left _ _ hL)) (Ideal.mul_mem_left _ _ hR')
    | add s t hs ht =>
      have := add_mem hs ht
      convert this using 1
      simp only [map_add (f := _)]; abel
  have hkill : ∀ a ∈ J, Δ'' a = 0 := by
    have h0 : Δ'' e' = 0 := by
      apply (he'.map Δ'').eq_zero_of_isNilpotent
      have := mem_nilradical.1 (key (Δ'' e'))
      rwa [hφΔ, he'0, map_zero, sub_zero] at this
    intro a ha
    rw [hJe] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  let Δ' : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Ideal.Quotient.liftₐ J Δ'' hkill
  have hΔ' : ∀ a, Δ' (mk a) = Algebra.TensorProduct.map mk mk (Δ a) := fun a => rfl
  refine ⟨ε', Δ', ⟨?_, ?_⟩, ?_⟩
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.lid k (A ⧸ J) (LinearMap.rTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hL]
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.rid k (A ⧸ J) (LinearMap.lTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hR]
  · rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro y hy
    exact mem_nilradical.2 (hnil y hy)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp
section
namespace GlobalTheory

theorem away_range_le_of_dvd (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R)
    (hcc : c ∣ c') (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P)
    (hκ : κ.comp (algebraMap R (Localization.Away c)) = g)
    (hκ' : κ'.comp (algebraMap R (Localization.Away c')) = g) : κ.range ≤ κ'.range := by
  have hu : IsUnit (algebraMap R (Localization.Away c') c) :=
    isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')
  let φ : Localization.Away c →+* Localization.Away c' := IsLocalization.Away.lift c hu
  have hφ : (κ'.comp φ) = κ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [hκ, RingHom.comp_assoc]
    have : φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c') :=
      IsLocalization.Away.lift_comp c hu
    rw [this, hκ']
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hφ]; rfl⟩

theorem away_range_le_of_dvd' : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range :=
  fun R _ P _ g c c' h κ κ' hκ hκ' => away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalars
section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end GlobalTheory
end

