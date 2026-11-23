module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroWindow

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma norm_sub_two_add_le_of_mem_strip {ρ : ℂ} {t : ℝ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht : |ρ.im - t| ≤ 1) : ‖ρ - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
  have him : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  rw [hre, him, abs_of_neg (by linarith)]
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma finsum_mem_le_of_subset_of_nonneg {S D : Set ℂ} (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hD : D.Finite) (hSD : S ⊆ D) :
    ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ D, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f (hD.subset hSD), finsum_mem_eq_finite_toFinset_sum f hD]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hSD) (fun x _ _ => hf x)


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.ZeroWindow.count_zeros_window : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨C1, hC1, hL⟩ := _root_.GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C2, hC2, hZ⟩ := _root_.GlobalTheory.ZetaWide.main
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun N _ χ hχ t => ?_⟩
  set s : ℂ := 2 + (t : ℂ) * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  by_cases h1χ : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1χ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    have hLz : LFunction χ = riemannZeta := LFunction_modOne_eq
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre] at this
      norm_num at this
    obtain ⟨hfin, hsum, -⟩ := hZ s (by rw [hsre]; norm_num) (by rw [hsre]) hs1
      (riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; norm_num))
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      refine ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, ?_, by rwa [hLz] at h3⟩
      rintro rfl
      simp at h1
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
          ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
          rw [hLz]
          exact finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin
            (by rw [hLz] at hsub; exact hsub)
      _ ≤ C2 * Real.log (|t| + 2) := hsum
      _ ≤ max C1 C2 * Real.log (((1 : ℕ) : ℝ) * (|t| + 2)) := by
          rw [Nat.cast_one, one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by linarith))
  · have hLs : LFunction χ s ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl h1χ) (by rw [hsre]; norm_num)
    obtain ⟨hfin, hsum, -⟩ := hL N χ h1χ s (by rw [hsre]; norm_num) (by rw [hsre]) hLs
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      exact ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, h3⟩
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) :=
          finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin hsub
      _ ≤ C1 * Real.log (N * (|t| + 2)) := hsum
      _ ≤ max C1 C2 * Real.log (N * (|t| + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.log_nonneg (by nlinarith))

end GlobalTheory.ZeroWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasures
section
open MeasureTheory Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.QuadFibre

theorem exists_map_div_eq_smul {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (fun t : K => t / a) ν = c • ν := by
  refine ⟨distribHaarChar K (Units.mk0 a ha), (distribHaarChar_pos).ne', ?_⟩
  ext S hS
  have hpre : (fun t : K => t / a) ⁻¹' S = (Units.mk0 a ha) • S := by
    ext t
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul, div_eq_inv_mul]
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  rw [Measure.map_apply hf hS, hpre, ← distribHaarChar_mul ν,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem avg_div_eq {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0)
    {U : Set K} (hU : MeasurableSet U) {g : K → ℝ≥0∞} (hg : Measurable g) :
    (ν {r | r / a ∈ U})⁻¹ * ∫⁻ t, g (t / a) ∂ν = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by
  obtain ⟨c, hc0, hc⟩ := exists_map_div_eq_smul ν ha
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  have hcU : ν {r | r / a ∈ U} = c * ν U := by
    have h : (Measure.map (fun t : K => t / a) ν) U = (c • ν) U := by rw [hc]
    rwa [Measure.map_apply hf hU, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcI : ∫⁻ t, g (t / a) ∂ν = c * ∫⁻ u, g u ∂ν := by
    rw [← lintegral_map hg hf, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcc : (c : ℝ≥0∞)⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0' ENNReal.coe_ne_top
  rw [hcU, hcI, ENNReal.mul_inv (Or.inl hc0') (Or.inl ENNReal.coe_ne_top)]
  calc (c : ℝ≥0∞)⁻¹ * (ν U)⁻¹ * (c * ∫⁻ u, g u ∂ν)
      = (ν U)⁻¹ * (∫⁻ u, g u ∂ν) * ((c : ℝ≥0∞)⁻¹ * c) := by ring
    _ = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by rw [hcc, mul_one]

theorem disintegration (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K)
    (hq : Continuous q) (hq2 : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (hU : IsSqrtOn U s)
    (hμ : ∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ)
    (h0 : μ {x | q x = 0} = 0) (φ : V → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := by
  obtain ⟨hUo, hUc, h1U, hmulU, hinvU, hnormU, hs, hsq⟩ := hU
  have hUm : MeasurableSet U := hUo.measurableSet
  have hνU0 : ν U ≠ 0 := hUo.measure_ne_zero ν ⟨1, h1U⟩
  have hνUt : ν U ≠ ∞ := hUc.measure_lt_top.ne
  have hqm : Measurable q := hq.measurable
  have hsm : Measurable s := hs.measurable
  have h0U : (0 : K) ∉ U := fun h => by simpa using hnormU 0 h
  have hdiv : Measurable (fun p : K × K => p.1 / p.2) := by
    simp_rw [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv
  have hself : ∀ t : K, t ∈ t • U := fun t => by simpa using Set.smul_mem_smul_set (a := t) h1U

  have hstab : ∀ u ∈ U, u • U = U := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => h0U (h ▸ hu)
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hu0, smul_eq_mul]
    constructor
    · intro h
      have := hmulU _ hu _ h
      rwa [← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at this
    · intro h
      exact hmulU _ (hinvU _ hu) _ h
  have hshift : ∀ t : K, ∀ t' ∈ t • U, t' • U = t • U := by
    intro t t' ht'
    obtain ⟨u, hu, rfl⟩ := ht'
    change (t • u) • U = t • U
    rw [smul_eq_mul, ← smul_smul, hstab u hu]
  have hmem : ∀ t : K, t ≠ 0 → ∀ y : K, y ∈ t • U ↔ t / y ∈ U := by
    intro t ht y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht, smul_eq_mul]
    constructor
    · intro h
      have := hinvU _ h
      rwa [mul_inv, inv_inv, ← div_eq_mul_inv] at this
    · intro h
      have := hinvU _ h
      rwa [inv_div, div_eq_inv_mul] at this
  have hpos : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    (hUo.smul₀ ht).measure_ne_zero ν ⟨t, hself t⟩

  have hmeas : Measurable (fun t : K => ν (t • U)) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    intro t ht
    have ht0 : t ≠ 0 := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hnb : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun _ : K => ν (t • U)) =ᶠ[𝓝 t] fun t' => ν (t' • U) := by
      filter_upwards [hnb] with t' ht'
      rw [hshift t t' ht']
    exact continuousAt_const.congr hev

  have hGm : Measurable (fun p : K × V => (ν (p.1 • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) p) := by
    refine (hmeas.comp measurable_fst).inv.mul (Measurable.indicator ?_ ?_)
    · exact hφ.comp ((hsm.comp (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd)))).smul
        measurable_snd)
    · exact (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd))) hUm

  have hA : ∀ t : K, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) = ∫⁻ x, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [fibOf_zero, lintegral_zero_measure]
      simp [h0U]
    · have hfm : Measurable (fun x : V => s (t / q x) • x) :=
        (hsm.comp (hdiv.comp (measurable_const.prodMk hqm))).smul measurable_id
      have hSm : MeasurableSet (q ⁻¹' (t • U)) := hqm (hUo.smul₀ ht).measurableSet
      rw [fibOf_ne μ ν q U s ht, lintegral_smul_measure, smul_eq_mul, lintegral_map hφ hfm,
        ← lintegral_indicator hSm, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (hpos t ht))]
      refine lintegral_congr fun x => ?_
      by_cases h : t / q x ∈ U
      · rw [Set.indicator_of_mem (show x ∈ q ⁻¹' (t • U) from (hmem t ht (q x)).mpr h),
          Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ q ⁻¹' (t • U) from fun h' => h ((hmem t ht (q x)).mp h')),
          Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h)]

  have hC : ∀ x : V, q x ≠ 0 → ∫⁻ t, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν =
      (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν := by
    intro x hx
    have hset : {r : K | r / q x ∈ U} = q x • U := by
      ext r
      rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, div_eq_inv_mul]
    have hpt : ∀ t : K, (ν (t • U))⁻¹ *
        {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) =
        (ν {r : K | r / q x ∈ U})⁻¹ * U.indicator (fun u => φ (s u • x)) (t / q x) := by
      intro t
      by_cases h : t / q x ∈ U
      · have ht' : t ∈ q x • U := by
          rw [Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, ← div_eq_inv_mul]
          exact h
        rw [Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_mem h, hset, hshift (q x) t ht']
      · rw [Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_notMem h, mul_zero, mul_zero]
    have hgm : Measurable (U.indicator (fun u => φ (s u • x))) :=
      (hφ.comp (hsm.smul measurable_const)).indicator hUm
    have hne : ν {r : K | r / q x ∈ U} ≠ 0 := by
      rw [hset]
      exact hpos _ hx
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hne)]
    exact avg_div_eq ν hx hUm hgm

  have hunit : ∀ u ∈ U, ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro u hu
    have hn : ‖s u‖ = 1 := by
      have h := congrArg norm (hsq u hu)
      rw [norm_pow, hnormU u hu] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
    calc ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂(Measure.map (fun x : V => s u • x) μ) :=
          (lintegral_map hφ (measurable_const_smul (s u))).symm
      _ = ∫⁻ x, φ x ∂μ := by rw [hμ _ hn]
  have hae : ∀ᵐ x ∂μ, q x ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  have hM2 : Measurable (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) := by
    have : (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) =
        (Prod.fst ⁻¹' U).indicator (fun p : K × V => φ (s p.1 • p.2)) := by
      funext p
      by_cases h : p.1 ∈ U
      · rw [Function.uncurry_apply_pair, Set.indicator_of_mem h,
          Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' U from h)]
      · rw [Function.uncurry_apply_pair, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' U from h)]
    rw [this]
    exact (hφ.comp ((hsm.comp measurable_fst).smul measurable_snd)).indicator (measurable_fst hUm)
  calc ∫⁻ x, φ x ∂μ = (ν U)⁻¹ * (ν U * ∫⁻ x, φ x ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hνU0 hνUt, one_mul]
    _ = (ν U)⁻¹ * ∫⁻ u, U.indicator (fun _ => ∫⁻ x, φ x ∂μ) u ∂ν := by
        rw [lintegral_indicator_const hUm, mul_comm (ν U)]
    _ = (ν U)⁻¹ * ∫⁻ u, ∫⁻ x, U.indicator (fun u => φ (s u • x)) u ∂μ ∂ν := by
        congr 1
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ U
        · simp [hu, hunit u hu]
        · simp [hu]
    _ = (ν U)⁻¹ * ∫⁻ x, ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_lintegral_swap hM2.aemeasurable]
    _ = ∫⁻ x, (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hνU0)]
    _ = ∫⁻ x, ∫⁻ t, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        exact (hC x hx).symm
    _ = ∫⁻ t, ∫⁻ x, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ ∂ν :=
        (lintegral_lintegral_swap hGm.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := lintegral_congr fun t => (hA t).symm

end GlobalTheory.QuadFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegrableContinuousOnAveragedFibreIntegral
section
open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.QuadFibre

theorem IsSqrtOn.div_mem_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t y : K} (h0 : t₀ ≠ 0) (ht : t ∈ t₀ • U) (hy : y ∈ t₀ • U) :
    y ≠ 0 ∧ t / y ∈ U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht hy
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨b, hb, rfl⟩ := hy
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hnorm b hb
    rw [hb0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨smul_ne_zero h0 hb0, ?_⟩
  simp only [smul_eq_mul]
  rw [mul_div_mul_left a b h0, div_eq_mul_inv]
  exact hmul a ha _ (hinv b hb)

theorem IsSqrtOn.smul_eq_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t : K} (ht : t ∈ t₀ • U) : t • U = t₀ • U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  have ha0 : a ≠ 0 := by
    intro ha0
    have := hnorm a ha
    rw [ha0, norm_zero] at this
    exact zero_ne_one this
  have haU : a • U = U := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hmul a ha b hb
    · intro hx
      refine ⟨a⁻¹ * x, hmul _ (hinv a ha) x hx, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [smul_eq_mul, mul_smul, haU]

theorem IsSqrtOn.norm_sqrt {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {a : K} (ha : a ∈ U) : ‖s a‖ = 1 := by
  obtain ⟨-, -, -, -, -, hnorm, -, hsq⟩ := h
  have h2 : ‖s a‖ ^ 2 = 1 := by rw [← norm_pow, hsq a ha, hnorm a ha]
  have h0 := norm_nonneg (s a)
  nlinarith [sq_nonneg (‖s a‖ - 1)]

theorem exists_integrable_bound_unit_smul {K V : Type} [NormedField K] [ProperSpace K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousSMul K V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ g : V → ℝ, Integrable g μ ∧ ∀ (a : K) (x : V), ‖a‖ = 1 → ‖φ (a • x)‖ ≤ g x := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set T : Set V := Metric.sphere (0 : K) 1 • tsupport φ with hTdef
  have hT : IsCompact T := by
    have := ((isCompact_sphere (0 : K) 1).prod hc).image (f := fun p : K × V => p.1 • p.2) continuous_smul
    rwa [Set.image_smul_prod] at this
  refine ⟨T.indicator (fun _ => C), ?_, ?_⟩
  · exact (integrable_indicator_iff hT.isClosed.measurableSet).mpr
      (integrableOn_const hT.measure_lt_top.ne)
  · intro a x ha
    by_cases hx : φ (a • x) = 0
    · rw [hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) x
    · have ha0 : a ≠ 0 := by
        rintro rfl
        rw [norm_zero] at ha
        exact zero_ne_one ha
      have hmem : x ∈ T := by
        refine Set.mem_smul.mpr ⟨a⁻¹, ?_, a • x, subset_tsupport _ (Function.mem_support.mpr hx),
          inv_smul_smul₀ ha0 x⟩
        rw [mem_sphere_zero_iff_norm, norm_inv, ha, inv_one]
      rw [Set.indicator_of_mem hmem]
      exact hC _

theorem integrable_and_continuousOn_fibOf (K V : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (q : V → K) (hq : Continuous q) (_hh : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (h : IsSqrtOn U s) (φ : V → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∀ t : K, t ≠ 0 → Integrable φ (fibOf μ ν q U s t)) ∧
      ContinuousOn (fun t => ∫ x, φ x ∂(fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  have h' := h
  obtain ⟨hUo, -, h1, -, -, -, hs, -⟩ := h'
  have hmf : ∀ t' : K, Measurable (fun x : V => s (t' / q x) • x) := by
    intro t'
    have hd : Measurable (fun x : V => t' / q x) := by
      simp_rw [div_eq_mul_inv]
      exact (hq.measurable.inv).const_mul t'
    exact (hs.measurable.comp hd).smul measurable_id
  obtain ⟨g, hg, hgb⟩ := exists_integrable_bound_unit_smul (K := K) μ hφ hc
  have hset : ∀ t : K, t ≠ 0 → MeasurableSet (q ⁻¹' (t • U)) := fun t ht =>
    (hUo.smul₀ ht).measurableSet.preimage hq.measurable
  have hself : ∀ t : K, t ∈ t • U := fun t => by
    simpa using Set.smul_mem_smul_set (a := t) h1
  have hν : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    ((hUo.smul₀ ht).measure_pos ν ⟨t, hself t⟩).ne'
  have hbd : ∀ t t' : K, t ≠ 0 → t' ∈ t • U → ∀ x ∈ q ⁻¹' (t • U), ‖φ (s (t' / q x) • x)‖ ≤ g x :=
    fun t t' ht ht' x hx => hgb _ x (h.norm_sqrt (h.div_mem_of_mem_smul ht ht' hx).2)
  have hint : ∀ t : K, t ≠ 0 →
      Integrable (fun x => φ (s (t / q x) • x)) (μ.restrict (q ⁻¹' (t • U))) := by
    intro t ht
    refine Integrable.mono' hg.restrict (hφ.measurable.comp (hmf t)).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (hset t ht)).mpr
      (Filter.Eventually.of_forall (fun x hx => hbd t t ht (hself t) x hx))
  have heq : ∀ t : K, t ≠ 0 → ∀ t' ∈ t • U, ∫ x, φ x ∂(fibOf μ ν q U s t') =
      (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ := by
    intro t ht t' ht'
    have ht'0 : t' ≠ 0 := (h.div_mem_of_mem_smul ht ht' ht').1
    rw [fibOf_ne μ ν q U s ht'0, h.smul_eq_of_mem_smul ht', integral_smul_measure,
      integral_map (hmf t').aemeasurable hφ.aestronglyMeasurable]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [fibOf_ne μ ν q U s ht]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hν t ht))
    exact (integrable_map_measure hφ.aestronglyMeasurable (hmf t).aemeasurable).mpr (hint t ht)
  · have ht0 : t ≠ 0 := ht
    apply ContinuousAt.continuousWithinAt
    have hnhds : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun t' => (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ)
        =ᶠ[𝓝 t] (fun t' => ∫ x, φ x ∂(fibOf μ ν q U s t')) :=
      Filter.eventually_of_mem hnhds (fun t' ht' => (heq t ht0 t' ht').symm)
    refine ContinuousAt.congr (ContinuousAt.const_smul (continuousAt_of_dominated
      (F := fun t' x => φ (s (t' / q x) • x)) (bound := g) ?_ ?_ hg.restrict ?_)
      ((ν (t • U))⁻¹.toReal)) hev
    · exact Filter.Eventually.of_forall
        (fun t' => (hφ.measurable.comp (hmf t')).aestronglyMeasurable)
    · exact Filter.eventually_of_mem hnhds (fun t' ht' => (ae_restrict_iff' (hset t ht0)).mpr
        (Filter.Eventually.of_forall (fun x hx => hbd t t' ht0 ht' x hx)))
    · exact Filter.Eventually.of_forall (fun x =>
        (hφ.comp ((hs.comp (continuous_id.div_const _)).smul continuous_const)).continuousAt)

end GlobalTheory.QuadFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular

theorem modularCharacter_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by
  haveI := hG Measure.haar inferInstance
  change Measure.modularCharacterFun g = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]
  have key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant],
      μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1 := by
    intro μ' _ _ h
    subst h
    exact Measure.haarScalarFactor_self _
  exact key _ (map_mul_right_eq_self _ g)

theorem invariantMeasureClause : InvariantMeasureClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH uG uH
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine _root_.GlobalTheory.WeilCriterion.modulusClause G H hH fun h => ?_
  rw [modularCharacter_eq_one uG, modularCharacter_eq_one uH]

end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
end

