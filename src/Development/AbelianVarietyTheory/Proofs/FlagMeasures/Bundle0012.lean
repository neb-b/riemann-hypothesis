module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfLintegralSmoothEq
section
open MeasureTheory

namespace GlobalTheory

theorem measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq {N : ℕ} (m₁ m₂ : Measure (Fin N → ℝ))
    (h : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U) (hb : Bornology.IsBounded U) : m₁ U = m₂ U := by

  obtain ⟨f, hfs, hfd, hfr⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have hfU : ∀ x, x ∉ U → f x = 0 := fun x hx => by
    rw [← hfs] at hx; simpa using hx
  have hfpos : ∀ x, x ∈ U → 0 < f x := fun x hx => by
    rw [← hfs] at hx; exact lt_of_le_of_ne (hf0 x) (Ne.symm hx)

  set φ : ℕ → (Fin N → ℝ) → ℝ := fun n x => Real.smoothTransition ((n : ℝ) * f x) with hφdef
  have hφd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hfd)
  have hφU : ∀ n x, x ∉ U → φ n x = 0 := fun n x hx => by
    simp [hφdef, hfU x hx]
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    HasCompactSupport.intro hK fun x hx => hφU n x fun hxU => hx (subset_closure hxU)
  have hφn : ∀ n x, 0 ≤ φ n x := fun n x => Real.smoothTransition.nonneg _
  have key : ∀ m : Measure (Fin N → ℝ),
      Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ n x) ∂m) Filter.atTop (nhds (m U)) := by
    intro m
    rw [← lintegral_indicator_one hU.measurableSet]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hφd n).continuous.measurable.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun x i j hij => ?_) (Filter.Eventually.of_forall fun x => ?_)
    · exact ENNReal.ofReal_le_ofReal (Real.smoothTransition.monotone
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) (hf0 x)))
    · by_cases hx : x ∈ U
      · have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * f x) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.atTop_mul_const (hfpos x hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually_ge_atTop 1] with n hn
        simp [hφdef, Real.smoothTransition.one_of_one_le hn, hx]
      · simp [hφU _ x hx, hx]
  exact tendsto_nhds_unique (key m₁)
    ((key m₂).congr fun n => (h (φ n) (hφd n) (hφc n) (hφn n)).symm)

theorem measure_eq_of_lintegral_smooth_eq :
    ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂],
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) →
      m₁ = m₂ := by
  intro N m₁ m₂ _ h

  let C : Set (Set (Fin N → ℝ)) := {s | IsOpen s ∧ Bornology.IsBounded s}
  have hgen : (inferInstance : MeasurableSpace (Fin N → ℝ)) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := Fin N → ℝ)]
      refine MeasurableSpace.generateFrom_le fun s hs => ?_
      have hs' : s = ⋃ n : ℕ, s ∩ Metric.ball 0 ((n : ℝ) + 1) := by
        rw [← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
      rw [hs']
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨by exact IsOpen.inter hs Metric.isOpen_ball, Metric.isBounded_ball.subset Set.inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun s hs => hs.1.measurableSet
  have hpi : IsPiSystem C := fun s hs t ht _ =>
    ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩
  refine (Measure.ext_of_generateFrom_of_iUnion C (fun n : ℕ => Metric.ball (0 : Fin N → ℝ) ((n : ℝ) + 1))
    hgen hpi (Metric.iUnion_ball_nat_succ _) (fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩)
    (fun n => measure_ball_lt_top.ne) fun s hs => ?_).symm
  exact (measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq m₁ m₂ h s hs.1 hs.2).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLe
section
namespace GlobalTheory.CoordScale
open MeasureTheory

theorem sigmaFinite_smul {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have h : c • μ = c.toNNReal • μ := by
    rw [ENNReal.smul_def, ENNReal.coe_toNNReal hc]
  rw [h]
  infer_instance

theorem pi_smul_ne_top {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := fun i => sigmaFinite_smul (μ i) (hc i)
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem measurePreserving_inv_mul (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by
  refine ⟨measurable_id.const_mul _, ?_⟩
  have hfun : (fun z : ℂ => ((r : ℂ))⁻¹ * z) = fun z => (r⁻¹ : ℝ) • z := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_pos (by positivity)]

private theorem map_pi_reindex_eq_pi_of_map_eq {ι ι' β γ : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    [MeasurableSpace γ] (e : ι ≃ ι') (μ : Measure β) [SigmaFinite μ] (ν : ι → Measure γ)
    [∀ i, SigmaFinite (ν i)] (h : ι → β → γ) (hh : ∀ i, Measurable (h i))
    (hmap : ∀ i, Measure.map (h i) μ = ν i) :
    Measure.map (fun (x : ι' → β) (i : ι) => h i (x (e i))) (Measure.pi fun _ => μ) =
      Measure.pi ν := by
  have hm : Measurable (fun (x : ι' → β) (i : ι) => h i (x (e i))) :=
    Measurable.of_eval (fun i => (hh i).comp (measurable_pi_apply (e i)))
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι' → β) (i : ι) => h i (x (e i))) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i' => h (e.symm i') ⁻¹' s (e.symm i')) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hx i'
      have := hx (e.symm i')
      rwa [Equiv.apply_symm_apply] at this
    · intro hx i
      have := hx (e i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  refine (Finset.prod_congr rfl (fun i' _ => ?_)).trans (Equiv.prod_comp e.symm (fun i => ν i (s i)))
  rw [← hmap (e.symm i'), Measure.map_apply (hh _) (hs _)]

theorem measure_preimage_reindex_scale_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  intro ι ι' κ κ' _ _ _ _ e f ρ c d hρ hc A hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  set C : ENNReal := ENNReal.ofReal c with hCdef
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have : SigmaFinite (C • (volume : Measure ℂ)) := sigmaFinite_smul _ hCt
  set w : κ → ENNReal := fun q => C * ENNReal.ofReal ((ρ ^ d q) ^ 2) with hwdef
  have hwt : ∀ q, w q ≠ ⊤ := fun q => ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  have : ∀ q, SigmaFinite (w q • (volume : Measure ℂ)) := fun q => sigmaFinite_smul _ (hwt q)
  have hin : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) =
      Measure.pi fun q : κ => w q • (volume : Measure ℂ) := by
    refine map_pi_reindex_eq_pi_of_map_eq f (C • (volume : Measure ℂ)) (fun q => w q • (volume : Measure ℂ))
      (fun q z => ((ρ : ℂ) ^ d q)⁻¹ * z) (fun q => measurable_const.mul measurable_id) (fun q => ?_)
    show Measure.map (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) (C • volume) = w q • volume
    have hfun : (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) = fun z => (((ρ ^ d q : ℝ) : ℂ))⁻¹ * z := by
      funext z
      rw [Complex.ofReal_pow]
    rw [hfun, Measure.map_smul (R := ENNReal) C
      (hf := (measurable_const_mul _).aemeasurable),
      (measurePreserving_inv_mul (ρ ^ d q) (pow_pos hρ0 _)).map_eq,
      smul_smul]
  set K : ENNReal := ∏ q, w q with hKdef
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun q _ => hwt q)
  have hin' : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) = K • (volume : Measure (κ → ℂ)) := by
    rw [hin, pi_smul_ne_top (fun _ => (volume : Measure ℂ)) w hwt]
    rfl
  have : SigmaFinite (K • (volume : Measure (κ → ℂ))) := sigmaFinite_smul _ hKt
  have hinm : Measurable (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) :=
    Measurable.of_eval (fun q => (measurable_pi_apply (f q)).const_mul _)
  have hout : Measure.map (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q))
      (MeasureTheory.Measure.pi fun _ : ι' =>
        MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) =
      (K ^ Fintype.card ι) • (volume : Measure (ι → κ → ℂ)) := by
    have h1 := map_pi_reindex_eq_pi_of_map_eq e (Measure.pi fun _ : κ' => C • (volume : Measure ℂ))
      (fun _ : ι => K • (volume : Measure (κ → ℂ)))
      (fun _ (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) (fun _ => hinm) (fun _ => hin')
    refine h1.trans ?_
    rw [pi_smul_ne_top (fun _ : ι => (volume : Measure (κ → ℂ))) (fun _ => K) (fun _ => hKt),
      Finset.prod_const, Finset.card_univ]
    rfl
  have hgm : Measurable (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) :=
    Measurable.of_eval (fun i => hinm.comp (measurable_pi_apply (e i)))
  rw [← Measure.map_apply hgm hA, hout, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hC1 : C ≤ 1 := ENNReal.ofReal_le_one.mpr hc
  have hK1 : K ≤ ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) := by
    refine Finset.prod_le_prod' (fun q _ => ?_)
    calc w q = C * ENNReal.ofReal ((ρ ^ d q) ^ 2) := rfl
      _ ≤ 1 * ENNReal.ofReal ((ρ ^ d q) ^ 2) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ d q) ^ 2) := one_mul _
  have hprod : ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) = ENNReal.ofReal (∏ q, (ρ ^ d q) ^ 2) :=
    (ENNReal.ofReal_prod_of_nonneg (fun q _ => by positivity)).symm
  have hreal : (∏ q, (ρ ^ d q) ^ 2) ^ Fintype.card ι = ρ ^ (2 * Fintype.card ι * ∑ q, d q) := by
    rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hK2 : K ^ Fintype.card ι ≤ ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
    rw [← hreal, ENNReal.ofReal_pow (by positivity), ← hprod]
    exact pow_le_pow_left' hK1 _
  gcongr

end GlobalTheory.CoordScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ModerateLogFactorAbsorbed
section
open Matrix Finset Real

namespace GlobalTheory

theorem moderate_log_factor_absorbed : ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (n f q : ℕ) (rd g b : ℝ), n₀ ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log rd ≤ Real.exp n → Real.log f ≤ Real.sqrt n → 2 ≤ b → Real.log b ≤ Real.exp (1 / 16 * n * f * Real.log n) → 1 ≤ g → g ≤ b ^ Cg → 2 * f * q * (11 * q * Real.log (n * f * rd * g * b)) ≤ Real.exp (1 / 8 * n * f * Real.log n) ∧ 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * Real.log n) ≤ Real.exp (-(1 / 4) * n * f * Real.log n) := by
  intro Cg
  set K : ℝ := 22 * (|Cg| + 4) with hK
  have hC : 0 ≤ |Cg| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩
  intro n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb
  have hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_exp (by positivity)) hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 16 * (1 + K) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  set L := Real.log n with hLdef
  have hm1 : (n : ℝ) ≤ n * f := by nlinarith
  have hm : (1 : ℝ) ≤ n * f := by linarith
  have hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L := by nlinarith
  set E := Real.exp (1 / 16 * n * f * L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEn : Real.exp n ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hnE : (n : ℝ) ≤ E := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  constructor
  · have hb0 : 0 < b := by linarith
    have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have h1 : L ≤ E := by
      have := Real.log_le_sub_one_of_pos hn0; linarith
    have h2 : Real.log f ≤ E := by
      have : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
      linarith
    have h3 : Real.log g ≤ |Cg| * E := by
      have h4 : Real.log g ≤ Real.log (b ^ Cg) := Real.log_le_log (by linarith) hgb
      rw [Real.log_rpow hb0] at h4
      have h5 : Cg * Real.log b ≤ |Cg| * Real.log b :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlb0
      have h6 : |Cg| * Real.log b ≤ |Cg| * E := mul_le_mul_of_nonneg_left hlb hC
      linarith
    have hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E := by
      have hf0 : (0 : ℝ) < f := by linarith
      have hrd0 : 0 < rd := by linarith
      have hg0 : 0 < g := by linarith
      rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne',
        Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']
      linarith
    have hKE : (n * f : ℝ) * K ≤ E := by
      have a1 : (n * f : ℝ) ≤ Real.exp (n * f) := by
        have := Real.add_one_le_exp (n * f : ℝ); linarith
      have a2 : K ≤ Real.exp K := by
        have := Real.add_one_le_exp K; linarith
      calc (n * f : ℝ) * K ≤ Real.exp (n * f) * Real.exp K :=
            mul_le_mul a1 a2 hK0 (Real.exp_pos _).le
        _ = Real.exp (n * f + K) := (Real.exp_add _ _).symm
        _ ≤ E := Real.exp_le_exp.mpr hX2
    have hEE : Real.exp (1 / 8 * n * f * L) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [hEE]
    calc 2 * (f : ℝ) * q * (11 * q * Real.log (n * f * rd * g * b))
        = (22 * f * q ^ 2) * Real.log (n * f * rd * g * b) := by ring
      _ ≤ (22 * f * q ^ 2) * ((|Cg| + 4) * E) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (22 * f * n) * ((|Cg| + 4) * E) := by gcongr
      _ = (n * f * K) * E := by rw [hK]; ring
      _ ≤ E * E := by gcongr
  · have hqn2 : (q : ℝ) ≤ n := by nlinarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : (2 : ℝ) ^ q ≤ Real.exp q := by
      calc (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := by gcongr
        _ = Real.exp q := by rw [← Real.exp_nat_mul]; simp
    calc 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * L)
        ≤ Real.exp 1 * Real.exp q * Real.exp (-(3 / 8) * n * f * L) := by gcongr
      _ = Real.exp (1 + q + -(3 / 8) * n * f * L) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
section
open NumberField

namespace GlobalTheory

theorem ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated
section
open Matrix Finset Real

namespace GlobalTheory


open MeasureTheory Metric in
theorem card_le_of_separated_in_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) (R la : ℝ) (hR : 0 ≤ R) (hla : 0 < la)
    (hT : ∀ x ∈ T, ‖x‖ ≤ R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → la ≤ ‖x - y‖) :
    (T.card : ℝ) ≤ (1 + 2 * R / la) ^ Module.finrank ℝ E := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : T.card ≤ 1 := Finset.card_le_one_of_subsingleton T
    rw [Module.finrank_zero_of_subsingleton, pow_zero]
    exact_mod_cast h1
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hr : 0 < la / 2 := by positivity
  have hdisj : (T : Set E).PairwiseDisjoint (fun x => ball x (la / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    rw [mem_ball, dist_eq_norm] at hzx hzy
    have h1 := hsep x hx y hy hxy
    have h2 : ‖x - y‖ < la := by
      calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
        _ < la / 2 + la / 2 := add_lt_add hzy hzx
        _ = la := by ring
    linarith
  have hsub : (⋃ x ∈ T, ball x (la / 2)) ⊆ ball (0 : E) (R + la / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_eq_norm] at hzx ⊢
    calc ‖z - 0‖ = ‖(z - x) + x‖ := by simp
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < la / 2 + R := by linarith [hT x hx]
      _ = R + la / 2 := by ring
  have hle := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_center, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball μ 0 hr.le, Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ R + la / 2),
    ← mul_assoc] at hle
  have hm0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hm0 hmtop, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : 0 < (la / 2) ^ Module.finrank ℝ E := by positivity
  have hq : (1 + 2 * R / la) ^ Module.finrank ℝ E
      = (R + la / 2) ^ Module.finrank ℝ E / (la / 2) ^ Module.finrank ℝ E := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [hq, le_div_iff₀ hpos]
  exact hle

theorem packing_geometric_mean_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : ι → Type) [∀ v, NormedAddCommGroup (W v)] [∀ v, NormedSpace ℝ (W v)] [∀ v, FiniteDimensional ℝ (W v)] (N : ℕ), 1 ≤ N → (∀ v, Module.finrank ℝ (W v) = N) → ∀ (la : ℝ) (S : Set (∀ v, W v)) (X : ι → ℝ), 0 < la → (∀ v, 0 < X v) → (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ≤ (∏ v, ‖s v - s' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → {s ∈ S | ∀ v, ‖s v‖ ≤ X v}.Finite ∧ (({s ∈ S | ∀ v, ‖s v‖ ≤ X v}.ncard : ℕ) : ℝ) ≤ (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ N hN hdim la S X hla hX hsep
  classical
  set k := Fintype.card ι with hk
  have hkpos : 0 < k := Fintype.card_pos
  set P := ∏ v, X v with hP
  have hPpos : 0 < P := Finset.prod_pos (fun v _ => hX v)
  set G := P ^ ((1 : ℝ) / k) with hG
  have hGpos : 0 < G := Real.rpow_pos_of_pos hPpos _
  have hGk : G ^ k = P := by
    rw [hG, one_div]
    exact Real.rpow_inv_natCast_pow hPpos.le hkpos.ne'
  set c : ι → ℝ := fun v => G / X v with hc
  have hcpos : ∀ v, 0 < c v := fun v => div_pos hGpos (hX v)
  have hcprod : ∏ v, c v = 1 := by
    rw [hc, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hk, hGk]
    exact div_self hPpos.ne'
  let φ : (∀ v, W v) → (∀ v, W v) := fun s v => c v • s v
  have hφinj : Function.Injective φ := by
    intro s s' h
    funext v
    exact smul_right_injective _ (hcpos v).ne' (congrFun h v)
  set A := {s ∈ S | ∀ v, ‖s v‖ ≤ X v} with hA
  have hdimPi : Module.finrank ℝ (∀ v, W v) = N * k := by
    rw [Module.finrank_pi_fintype]
    simp [hdim, hk, mul_comm]
  have key : ∀ F : Finset (∀ v, W v), (↑F : Set (∀ v, W v)) ⊆ A →
      (F.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * k) := by
    intro F hF
    have hbound := card_le_of_separated_in_ball (F.image φ) G la hGpos.le hla ?_ ?_
    · rw [Finset.card_image_of_injective _ hφinj, hdimPi] at hbound
      exact hbound
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      have hsA := hF hs
      refine (pi_norm_le_iff_of_nonneg hGpos.le).mpr (fun v => ?_)
      simp only [φ, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos v)]
      calc c v * ‖s v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hsA.2 v) (hcpos v).le
        _ = G := by
          simp only [hc]
          field_simp [(hX v).ne']
    · intro y hy y' hy' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy'
      have hss : s ≠ s' := fun h => hne (by rw [h])
      have h1 := hsep s (hF hs).1 s' (hF hs').1 hss
      have hprod : ∏ v, ‖(φ s - φ s') v‖ = ∏ v, ‖s v - s' v‖ := by
        simp only [φ, Pi.sub_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos _),
          Finset.prod_mul_distrib, hcprod, one_mul]
      have hgm : (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ ‖φ s - φ s'‖ := by
        have hle : ∏ v, ‖(φ s - φ s') v‖ ≤ ‖φ s - φ s'‖ ^ k := by
          rw [hk, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => norm_le_pi_norm _ v)
        calc (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ (‖φ s - φ s'‖ ^ k) ^ ((1 : ℝ) / k) :=
              Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => norm_nonneg _)) hle (by positivity)
          _ = ‖φ s - φ s'‖ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
                mul_one_div_cancel (by exact_mod_cast hkpos.ne'), Real.rpow_one]
      rw [hprod] at hgm
      exact h1.trans hgm
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (⌈(1 + 2 * G / la) ^ (N * k)⌉₊ + 1)
    have h3 := key F hF
    rw [hcard] at h3
    push_cast at h3
    linarith [Nat.le_ceil ((1 + 2 * G / la) ^ (N * k))]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact key _ (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.HaarDensChart

def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)

end GlobalTheory.HaarDensChart
end
end

