module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeak
section
open MeasureTheory Matrix Filter Topology

namespace GlobalTheory

theorem tendsto_integral_normalised_pow_peak :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  intro X _ _ _ _ μ hμ K x₀ f hK hKc hx₀ hpos hf hf1 hf01 hsep E _ _ _ F hF
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hKc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hKae
  have hFm : AEStronglyMeasurable F μ := by
    have h := hF.aestronglyMeasurable_of_isCompact (μ := μ) hK hKm
    rwa [hμK] at h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ hx₀)

  have hfm_int : ∀ m : ℕ, Integrable (fun x => f x ^ m) μ := by
    intro m
    refine Integrable.of_bound (hf.pow m).aestronglyMeasurable 1 ?_
    filter_upwards [hKae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf01 x hx).1 m)]
    exact pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2

  have hlow : ∀ η : ℝ, 0 ≤ η → ∀ m : ℕ,
      η ^ m * μ.real {x | η < f x} ≤ ∫ y, f y ^ m ∂μ := by
    intro η hη m
    have hWm : MeasurableSet {x | η < f x} := measurableSet_lt measurable_const hf.measurable
    have h := integral_indicator_const (μ := μ) (η ^ m) hWm
    rw [smul_eq_mul] at h
    rw [mul_comm, ← h]
    refine integral_mono_ae ((integrable_const (η ^ m)).indicator hWm) (hfm_int m) ?_
    filter_upwards [hKae] with x hx
    by_cases hxW : x ∈ {x | η < f x}
    · rw [Set.indicator_apply, if_pos hxW]
      exact pow_le_pow_left₀ hη (le_of_lt hxW) m
    · rw [Set.indicator_apply, if_neg hxW]
      exact pow_nonneg (hf01 x hx).1 m
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨u, hu_open, hx₀u, hu⟩ :=
    mem_nhdsWithin.mp ((hF x₀ hx₀) (Metric.ball_mem_nhds (F x₀) (half_pos hε)))
  obtain ⟨δ, hδ1, hδ⟩ := hsep u (hu_open.mem_nhds hx₀u)
  obtain ⟨d, hd0, hd1, hδd⟩ : ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ δ ≤ d :=
    ⟨max δ 0, le_max_right _ _, max_lt hδ1 one_pos, le_max_left _ _⟩
  obtain ⟨η, hη0, hdη, hη1⟩ : ∃ η : ℝ, 0 < η ∧ d < η ∧ η < 1 :=
    ⟨(d + 1) / 2, by linarith, by linarith, by linarith⟩
  have hWpos : 0 < μ {x | η < f x} :=
    hpos _ (isOpen_lt continuous_const hf) (by show η < f x₀; rw [hf1]; exact hη1)
  have hW : 0 < μ.real {x | η < f x} := ENNReal.toReal_pos hWpos.ne' (measure_ne_top μ _)
  have hr : Tendsto (fun m : ℕ => (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x})
      atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd0 hη0.le)
      ((div_lt_one hη0).mpr hdη)).const_mul (2 * C + 1)).div_const (μ.real {x | η < f x})
    simpa using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr (Iio_mem_nhds (half_pos hε)))
  refine ⟨N, fun m hm => ?_⟩
  have hIpos : 0 < ∫ y, f y ^ m ∂μ :=
    lt_of_lt_of_le (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  set c : X → ℂ := fun x => ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) with hc
  have hc_cont : Continuous c :=
    Complex.continuous_ofReal.comp ((hf.pow m).div_const _)
  have hcnorm : ∀ x ∈ K, ‖c x‖ = f x ^ m / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hc, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le)]
  have hcle : ∀ x ∈ K, ‖c x‖ ≤ 1 / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hcnorm x hx]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2) hIpos.le
  have hc_int : Integrable c μ := by
    refine Integrable.of_bound hc_cont.aestronglyMeasurable (1 / ∫ y, f y ^ m ∂μ) ?_
    filter_upwards [hKae] with x hx
    exact hcle x hx
  have hcF_int : Integrable (fun x => c x • F x) μ := by
    refine Integrable.of_bound (hc_cont.aestronglyMeasurable.smul hFm)
      (1 / (∫ y, f y ^ m ∂μ) * C) ?_
    filter_upwards [hKae] with x hx
    rw [norm_smul]
    exact mul_le_mul (hcle x hx) (hC x hx) (norm_nonneg _) (by positivity)

  have hint1 : ∫ x, c x ∂μ = 1 := by
    show ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_div, div_self hIpos.ne', Complex.ofReal_one]
  have hkey : (∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) - F x₀
      = ∫ x, c x • (F x - F x₀) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hcF_int (hc_int.smul_const (F x₀)), integral_smul_const, hint1, one_smul]
  set B : ℝ := (2 * C + 1) * d ^ m / ∫ y, f y ^ m ∂μ with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (by linarith) (pow_nonneg hd0 m)) hIpos.le
  have hbound : ∀ᵐ x ∂μ, ‖c x • (F x - F x₀)‖
      ≤ (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B := by
    filter_upwards [hKae] with x hx
    have h0 : 0 ≤ f x ^ m / ∫ y, f y ^ m ∂μ :=
      div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le
    rw [norm_smul, hcnorm x hx]
    by_cases hxu : x ∈ u
    · have hlt : ‖F x - F x₀‖ < ε / 2 := by
        have h := hu ⟨hxu, hx⟩
        simpa [dist_eq_norm] using h
      have := mul_le_mul_of_nonneg_left hlt.le h0
      linarith
    · have hfx : f x ≤ d := le_trans (hδ x hx hxu) hδd
      have hpow : f x ^ m ≤ d ^ m := pow_le_pow_left₀ (hf01 x hx).1 hfx m
      have hFd : ‖F x - F x₀‖ ≤ 2 * C + 1 := by
        have := norm_sub_le (F x) (F x₀)
        linarith [hC x hx, hC x₀ hx₀]
      have h1 : f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖ ≤ B := by
        calc f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖
            = (‖F x - F x₀‖ * f x ^ m) / ∫ y, f y ^ m ∂μ := by ring
          _ ≤ ((2 * C + 1) * d ^ m) / ∫ y, f y ^ m ∂μ :=
            div_le_div_of_nonneg_right
              (mul_le_mul hFd hpow (pow_nonneg (hf01 x hx).1 m) (by linarith)) hIpos.le
      have h2 : 0 ≤ f x ^ m / (∫ y, f y ^ m ∂μ) * (ε / 2) := mul_nonneg h0 (by linarith)
      linarith
  have hBle : B ≤ (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x} := by
    rw [hB, div_pow, mul_div_assoc', div_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (pow_nonneg hd0 m))
      (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  have hBlt : B < ε / 2 := lt_of_le_of_lt hBle (hN m hm)
  have hg_int : Integrable (fun x => (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) μ :=
    (((hfm_int m).div_const _).mul_const _).add (integrable_const _)
  rw [dist_eq_norm, hkey]
  calc ‖∫ x, c x • (F x - F x₀) ∂μ‖
      ≤ ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) ∂μ :=
        norm_integral_le_of_norm_le hg_int hbound
    _ = ε / 2 + B := by
        rw [integral_add (((hfm_int m).div_const _).mul_const _) (integrable_const _),
          integral_mul_const, integral_div, div_self hIpos.ne', integral_const]
        simp
    _ < ε := by linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurable
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem yv_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  intro k r z z' γ hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yv k r z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r r z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z' (Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z').2.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z (γ * Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z).2.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset k r z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yv k r z z' γ (Matrix.of x.1) ∧ Yv k r z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem sum_normSq_col {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (i : Fin n) :
    ∑ j, ‖g j i‖ ^ 2 = 1 := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg
  have h2 : (star g * g) i i = 1 := by rw [h1]; simp
  rw [Matrix.mul_apply] at h2
  have h3 : ((∑ j, ‖g j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h3

theorem norm_entry_le_one {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (j i : Fin n) :
    ‖g j i‖ ≤ 1 := by
  have h := sum_normSq_col hg i
  have h2 : ‖g j i‖ ^ 2 ≤ ∑ j, ‖g j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖g j i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h2
  nlinarith [norm_nonneg (g j i)]

theorem re_trace_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace g).re = ∑ i, (g i i).re := by
  simp [Matrix.trace, Complex.re_sum]

theorem eq_one_of_re_trace {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))
    (ht : (Matrix.trace g).re = n) : g = 1 := by
  have hle : ∀ i, (g i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (norm_entry_le_one hg i i)
  have hsum : ∑ i : Fin n, (1 - (g i i).re) = 0 := by
    rw [Finset.sum_sub_distrib, ← re_trace_eq, ht]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1 hsum
  have hre : ∀ i, (g i i).re = 1 := fun i => by
    have := hz i (Finset.mem_univ i)
    linarith
  have hnorm : ∀ i, ‖g i i‖ = 1 := fun i => le_antisymm (norm_entry_le_one hg i i)
    (by simpa [hre i] using Complex.re_le_norm (g i i))
  have hdiag : ∀ i, g i i = 1 := fun i => by
    have h1 : ‖g i i‖ ^ 2 = (g i i).re ^ 2 + (g i i).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hnorm i, hre i] at h1
    have him : (g i i).im = 0 := by nlinarith
    exact Complex.ext (by simpa using hre i) (by simpa using him)
  ext j i
  by_cases hji : j = i
  · subst hji
    simp [hdiag j]
  · have hs := sum_normSq_col hg i
    have h0 : ∑ k ∈ Finset.univ.erase i, ‖g k i‖ ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun k => ‖g k i‖ ^ 2) (Finset.mem_univ i)
      rw [hs, hnorm i] at this
      linarith
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h0
    have := hz2 j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have hn : ‖g j i‖ = 0 := by simpa using this
    rw [Matrix.one_apply_ne hji]
    exact norm_eq_zero.1 hn

theorem peak_continuous (n : ℕ) : Continuous (peak n) := by
  unfold peak
  have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace g).re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  fun_prop

theorem peak_one {n : ℕ} (hn : 0 < n) : peak n 1 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [peak, Matrix.trace_one, this]

theorem abs_re_trace_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    |(Matrix.trace g).re| ≤ n := by
  rw [re_trace_eq]
  calc |∑ i, (g i i).re| ≤ ∑ i, |(g i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (norm_entry_le_one hg i i)
    _ = n := by simp

theorem peak_mem_Icc {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    0 ≤ peak n g ∧ peak n g ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_le.1 (abs_re_trace_le hg)
  have h1 : -1 ≤ (Matrix.trace g).re / n := by
    rw [le_div_iff₀ hn']; linarith [h.1]
  have h2 : (Matrix.trace g).re / n ≤ 1 := by
    rw [div_le_iff₀ hn']; linarith [h.2]
  unfold peak
  constructor <;> linarith

theorem peak_lt_one {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (h1 : g ≠ 1) :
    peak n g < 1 := by
  refine lt_of_le_of_ne (peak_mem_Icc hn hg).2 fun he => h1 (eq_one_of_re_trace hg ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold peak at he
  have : (Matrix.trace g).re / n = 1 := by linarith
  field_simp at this
  linarith

theorem peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧
    (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
      0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧
    ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1,
      ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
        g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  intro n hn
  refine ⟨peak_continuous n, peak_one hn, fun g hg => peak_mem_Icc hn hg, fun U hU => ?_⟩
  have hK : IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) :=
    (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).inter_right isOpen_interior.isClosed_compl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  rcases Set.eq_empty_or_nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) with he | hne
  · refine ⟨0, by norm_num, fun g hg hgU => ?_⟩
    have : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ :=
      ⟨hg, fun hi => hgU (interior_subset hi)⟩
    rw [he] at this
    exact this.elim
  · obtain ⟨g₀, hg₀, hmax⟩ := hK.exists_isMaxOn hne (peak_continuous n).continuousOn
    have hne1 : g₀ ≠ 1 := fun h => hg₀.2 (h ▸ h1)
    refine ⟨peak n g₀, peak_lt_one hn hg₀.1 hne1, fun g hg hgU => ?_⟩
    exact hmax ⟨hg, fun hi => hgU (interior_subset hi)⟩

end GlobalTheory.KFinAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePo
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg.PeakPoly

def coord (n : ℕ) : Option ((Fin n × Fin n) × Bool) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | none, _ => 1
  | some ((i, j), false), g => g i j
  | some ((i, j), true), g => star (g i j)

theorem continuous_coord (n : ℕ) (d : Option ((Fin n × Fin n) × Bool)) : Continuous (coord n d) := by
  rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
  · exact continuous_const
  · exact continuous_id.matrix_elem i j
  · exact (continuous_id.matrix_elem i j).star

theorem prod_expand {ι D X : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    (x : D → X → ℂ) (c : ι → D → ℂ) (g : X) :
    ∏ j, ∑ e, c j e * x e g = ∑ t : ι → D, (∏ j, c j (t j)) * ∏ j, x (t j) g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]

theorem coord_translate (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (d : Option ((Fin n × Fin n) × Bool)) :
    ∃ T : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, coord n d (a * g) = ∑ e, T e * coord n e g := by
  have hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none := by
        funext g; rfl
      rw [this]; exact Submodule.subset_span ⟨none, rfl⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) =
          ∑ l, a i l • coord n (some ((l, j), false)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) =
          ∑ l, star (a i l) • coord n (some ((l, j), true)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply, star_sum]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨T, fun g => ?_⟩
  have := congrFun hT g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem peak_expand (n : ℕ) :
    ∃ c : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, ((peak n g : ℝ) : ℂ) = ∑ e, c e * coord n e g := by
  have hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    have : (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none +
        ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true))) := by
      funext g
      simp only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]
      push_cast
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace,
        map_sum]
      simp only [Matrix.diag, Complex.star_def]
      ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨c, fun g => ?_⟩
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

end GlobalTheory.KFinAvg.PeakPoly

namespace GlobalTheory.KFinAvg
open PeakPoly

theorem peak_pow_polynomial : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ),
    (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧
    ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  intro n m
  classical
  let e := Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))
  let bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun s g => ∏ j, coord n (s j) g
  obtain ⟨c0, hc0⟩ := peak_expand n
  refine ⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i),
    fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩
  · intro i
    exact continuous_finsetProd _ fun j _ => continuous_coord n _
  · intro g
    have h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g := by
      rw [Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm
  · intro a i
    choose T hT using fun j => coord_translate n a (e.symm i j)
    refine ⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩
    show ∏ j, coord n (e.symm i j) (a * g) = _
    simp_rw [hT]
    rw [prod_expand (fun d g => coord n d g) T g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm

end GlobalTheory.KFinAvg
end
end

