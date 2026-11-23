module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKappaPropertiesProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicKappaLemmas

open UpperTheory.Esk

theorem nsq (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pos_den {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

theorem kap_of {z w : P} (h : 0 < z.1.im * w.1.im) :
    kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
  unfold kap
  rw [if_pos h]

theorem kap_of_not {z w : P} (h : ¬ 0 < z.1.im * w.1.im) : kap z w = 0 := by
  unfold kap
  rw [if_neg h]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem key {z w u : ℂ} (h1 : 0 < z.im * w.im) (h2 : 0 < w.im * u.im) :
    w.im ^ 2 * ‖z - conj u‖ ^ 2 ≤ ‖z - conj w‖ ^ 2 * ‖w - conj u‖ ^ 2 := by
  have h13 : 0 < z.im * u.im := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.im)]
  have hp : 0 ≤ z.im ^ 2 + 2 * z.im * w.im := by nlinarith [sq_nonneg z.im]
  have hq : 0 ≤ u.im ^ 2 + 2 * w.im * u.im := by nlinarith [sq_nonneg u.im]
  rw [nsq, nsq, nsq]
  nlinarith [sq_nonneg ((z.re - w.re) * (w.re - u.re) - w.im ^ 2),
    mul_nonneg (sq_nonneg (z.re - w.re)) hq, mul_nonneg (sq_nonneg (w.re - u.re)) hp,
    mul_nonneg (sq_nonneg w.im) h1.le, mul_nonneg (sq_nonneg w.im) h2.le,
    mul_nonneg (sq_nonneg w.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
    sq_nonneg (z.im * u.im)]

theorem p1 (z w : P) : 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z := by
  refine ⟨kap_nonneg z w, ?_, ?_⟩
  · by_cases h : 0 < z.1.im * w.1.im
    · rw [kap_of h, div_le_iff₀ (pos_den h), nsq]
      nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
    · rw [kap_of_not h]
      norm_num
  · have e2 : ‖w.1 - conj z.1‖ ^ 2 = ‖z.1 - conj w.1‖ ^ 2 := by
      rw [nsq, nsq]
      ring
    unfold kap
    rw [mul_comm w.1.im z.1.im, e2]

theorem p2 (z : P) : kap z z = 1 := by
  have h : 0 < z.1.im * z.1.im := mul_self_pos.mpr z.2
  rw [kap_of h, div_eq_one_iff_eq (pos_den h).ne', nsq]
  ring

theorem p3 (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  by_cases h1 : 0 < z.1.im * w.1.im
  · by_cases h2 : 0 < w.1.im * u.1.im
    · have h13 : 0 < z.1.im * u.1.im := by
        by_contra hc
        have hc := not_lt.mp hc
        nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.1.im)]
      have hA := pos_den h1
      have hB := pos_den h2
      have hC := pos_den h13
      have hk := mul_le_mul_of_nonneg_left (key h1 h2) h13.le
      rw [kap_of h1, kap_of h2, kap_of h13, div_mul_div_comm, mul_div_assoc', le_div_iff₀ hC,
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hA hB)]
      nlinarith [hk]
    · rw [kap_of_not h2, mul_zero]
      exact mul_nonneg (by norm_num) (kap_nonneg z u)
  · rw [kap_of_not h1, zero_mul]
    exact mul_nonneg (by norm_num) (kap_nonneg z u)

theorem p4 (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  by_cases h : 0 < z.1.im * w.1.im
  · rw [kap_of h, div_mul_eq_mul_div, div_le_iff₀ (pos_den h), nsq]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith [h, hw]
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.mpr hw.le)]
    · have hz : 0 < z.1.im := by nlinarith [h, hw]
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)), mul_nonneg hz.le (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [kap_of_not h, zero_mul]
    positivity

theorem p5 : Continuous (fun p : P × P => kap p.1 p.2) := by
  have hv1 : Continuous (fun p : P × P => p.1.1) := continuous_subtype_val.comp continuous_fst
  have hv2 : Continuous (fun p : P × P => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun p : P × P => p.1.1.im * p.2.1.im) :=
    (Complex.continuous_im.comp hv1).mul (Complex.continuous_im.comp hv2)
  have hd : Continuous (fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2) :=
    ((hv1.sub (Complex.continuous_conj.comp hv2)).norm).pow 2
  have hopen : IsOpen {p : P × P | 0 < p.1.1.im * p.2.1.im} := isOpen_lt continuous_const hc
  have hclosed : IsClosed {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
    have e : {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (Ne.symm (mul_ne_zero p.1.2 p.2.2))⟩
    rw [e]
    exact isClosed_le continuous_const hc
  have hfr : frontier {p : P × P | 0 < p.1.1.im * p.2.1.im} = ∅ := by
    rw [frontier, hclosed.closure_eq, hopen.interior_eq, Set.sdiff_self]
  show Continuous (fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0)
  apply continuous_if
  · intro a ha
    simp [hfr] at ha
  · rw [hclosed.closure_eq]
    exact ((continuous_const.mul hc).continuousOn).div hd.continuousOn
      (fun p hp => (pos_den (z := p.1.1) (w := p.2.1) hp).ne')
  · exact continuousOn_const

theorem p6 (z : P) : ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hdet : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using z.2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, rfl, Subtype.ext ?_⟩
  rw [coe_smul]
  show num (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I /
    den (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I = z.1
  have h00 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 0 = z.1.im := rfl
  have h01 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 1 = z.1.re := rfl
  have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 0 = 0 := rfl
  have h11 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 1 = 1 := rfl
  rw [num, den, h00, h01, h10, h11]
  apply Complex.ext <;> simp

end UpperTheory.Esk.HyperbolicKappaLemmas

namespace UpperTheory.Esk

theorem hyperbolic_kappa_properties_proof : B1c := by
  unfold B1c
  exact ⟨HyperbolicKappaLemmas.p1, HyperbolicKappaLemmas.p2, HyperbolicKappaLemmas.p3, HyperbolicKappaLemmas.p4, HyperbolicKappaLemmas.p5, HyperbolicKappaLemmas.p6⟩

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.InverseSeriesSummable
section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UpperTheory.Esk.InverseSeriesLemmas

theorem enorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (x : ℂ) : ‖r • x‖ₑ = ENNReal.ofReal r * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal hr]

theorem hasSum_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : HasSum (fun g : G => b (g⁻¹ • y)) 1 := by
  have h := (Equiv.inv G).hasSum_iff.mpr (hb.sum y)
  exact h

theorem tsum_ofReal_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
  have hs := UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y
  calc ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ENNReal.ofReal (∑' g : G, b (g⁻¹ • y)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) hs.summable).symm
    _ = 1 := by rw [hs.tsum_eq, ENNReal.ofReal_one]

end UpperTheory.Esk.InverseSeriesLemmas

open UpperTheory.Esk.InverseSeriesLemmas in
theorem UpperTheory.Esk.inverse_series_summable : UpperTheory.Esk.C3 := by
  unfold UpperTheory.Esk.C3
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  have hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ := hμ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y := ⟨_, fun _ _ => rfl⟩
  have hΦm : ∀ g, Measurable (Φ g) := by
    intro g
    rw [show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]
    exact hb.meas.smul (hf.comp (hμ' g).measurable)
  have hΨm : ∀ g, Measurable (Ψ g) := by
    intro g
    rw [show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]
    exact (hb.meas.comp (hμ' g⁻¹).measurable).smul hf
  have emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y) := fun g =>
    (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding
  have hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := fun g =>
    lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])
  have hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    intro g
    rw [← (hμ' g).lintegral_comp (hΨm g).enorm]
    exact lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])
  have hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤ := hfi.2
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∑' g : G, ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          tsum_congr hΨl
      _ = ∫⁻ z, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          (lintegral_tsum (fun g =>
            ((hb.meas.comp (hμ' g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable)).symm
      _ = ∫⁻ z, ‖f z‖ₑ ∂μ := lintegral_congr (fun z => by
          rw [ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])
  have hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := (tsum_congr hΦl).trans hsumΨ
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤ := by rw [hsumΦ']; exact hfin.ne
  have hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ := by
    intro g
    rw [← (hμ' g).integral_comp (emb g) (Ψ g)]
    congr 1
    funext y
    rw [hΦ, hΨ, inv_smul_smul]
  have hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ :=
    integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)
  have hΨp : ∀ z, ∑' g, Ψ g z = f z := by
    intro z
    simp only [hΨ]
    rw [((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]
  have hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ :=
    integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ
  have hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y) := by
    intro y
    simp only [hΦ]
    exact tsum_const_smul'' (b y)
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y :=
    funext (fun y => (hΦp y).symm)
  have heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ := by
    rw [hfun, hΦt, tsum_congr hΦi, ← hΨt]
    congr 1
    funext z
    exact hΨp z
  have hint : Integrable (fun y => ∑' g, Φ g y) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩
    have hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ :=
      lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)
    have hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ :=
      lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)
    exact lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)
  exact ⟨by rw [hfun]; exact hint, heq⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfLinTr
section
noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.LinearTraceLemmas

variable {A Y : Type} [MeasurableSpace Y] (ν : Measure Y) (V : Submodule ℂ (A → ℂ))

def evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype

theorem evl_apply (a : A) (f : V) : evl V a f = f.1 a := rfl

theorem span_evl [FiniteDimensional ℂ V] : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective f
  have hv : v = 0 := by
    apply Subtype.ext
    funext a
    have h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0 :=
      LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a := by
      rfl
    have h3 : v.1 a = 0 := h2.symm.trans h1
    simpa using h3
  exact hf0 (by rw [hv, map_zero])

omit [MeasurableSpace Y] in
theorem bound_mul {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y) (C D : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) (y : Y) : ‖g y * h y‖ ≤ C * D := by
  have hn' := hn y
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * n y < 0 := mul_neg_of_neg_of_pos hlt hn'
    linarith [norm_nonneg (g y), hC y]
  rw [norm_mul]
  calc ‖g y‖ * ‖h y‖ ≤ (C * n y) * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    _ = C * (‖h y‖ * n y) := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0

theorem integrable_mul [IsFiniteMeasure ν] {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y)
    (hg : Measurable g) (hh : Measurable h) (C D : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * n y)
    (hD : ∀ y, ‖h y‖ * n y ≤ D) : Integrable (fun y => g y * h y) ν := by
  exact (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable
    (ae_of_all _ fun y => bound_mul hn C D hC hD y)

def Good (K : Y → V) (ev : Y → A) (n : Y → ℝ) (φ : Module.Dual ℂ V) : Prop :=
  Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧
    ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f

theorem good_all [IsFiniteMeasure ν] [FiniteDimensional ℂ V] (K : Y → V) (ev : Y → A) (n : Y → ℝ)
    (hn : ∀ y, 0 < n y) (hK : ∀ a, Measurable fun y => (K y).1 a)
    (hev : ∀ f : V, Measurable fun y => f.1 (ev y)) (hKb : ∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y)
    (hevb : ∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C)
    (hrep : ∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) (φ : Module.Dual ℂ V) :
    Good ν V K ev n φ := by
  have hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V,
      Integrable (fun y => ψ (K y) * f.1 (ev y)) ν := by
    intro ψ hψ f
    obtain ⟨C, hC⟩ := hψ.2.1
    obtain ⟨D, hD⟩ := hevb f
    exact integrable_mul ν hn hψ.1 (hev f) C D hC hD
  have hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂) := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := h₁.2.1
    obtain ⟨C₂, hC₂⟩ := h₂.2.1
    refine ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))
    · simp only [LinearMap.add_apply, add_mul]
      rw [integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]
  have hzero : Good ν V K ev n 0 := by
    refine ⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩
    · simp
    · simp
    · simp
  have hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ) := by
    intro c φ h
    obtain ⟨C, hC⟩ := h.2.1
    refine ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2.2 f]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ :=
    ⟨{ carrier := {ψ | Good ν V K ev n ψ}
       add_mem' := fun {a b} ha hb => hadd a b ha hb
       zero_mem' := hzero
       smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩
  have hev' : ∀ a, Good ν V K ev n (evl V a) := by
    intro a
    refine ⟨?_, ?_, fun f => ?_⟩
    · simpa only [evl_apply] using hK a
    · simpa only [evl_apply] using hKb a
    · simpa only [evl_apply] using hrep f a
  have htop : Sg = ⊤ := by
    rw [eq_top_iff, ← span_evl V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (hSg _).mpr (hev' a)
  exact (hSg φ).mp (by rw [htop]; exact Submodule.mem_top)

theorem main : UpperTheory.Esk.LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ :=
    good_all ν V K ev n hn hK hev hKb hevb hrep
  let b := Module.finBasis ℂ V
  have hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    intro y
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) := by
      conv_lhs => rw [← b.sum_repr (K y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e]
    simp [Module.Basis.coord_apply]
  have hmeas : Measurable fun y => (T (K y)).1 (ev y) := by
    simp_rw [hexp]
    exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))
  have hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C := by
    choose Cs hCs using fun i => (hgood (b.coord i)).2.1
    choose Ds hDs using fun i => hevb (T (b i))
    refine ⟨∑ i, Cs i * Ds i, fun y => ?_⟩
    rw [hexp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)
  have hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν := by
    intro i
    obtain ⟨C, hC⟩ := (hgood (b.coord i)).2.1
    obtain ⟨D, hD⟩ := hevb (T (b i))
    exact integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD
  refine ⟨hmeas, hbd, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hgood (b.coord i)).2.2 (T (b i))]
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end UpperTheory.Esk.LinearTraceLemmas

theorem UpperTheory.Esk.pf_LinTr : UpperTheory.Esk.LinTr := by
  exact UpperTheory.Esk.LinearTraceLemmas.main
end
end

