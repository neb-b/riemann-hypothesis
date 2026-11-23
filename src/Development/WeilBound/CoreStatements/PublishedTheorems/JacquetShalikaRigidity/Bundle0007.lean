module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogNormEstimates
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogNormEstimates

theorem log_le {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h1 : a ≤ D) (h2 : D ≤ b) :
    |Real.log D| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log hD h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem norm_le {p : ℂ} {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h : p ≠ 0 → a ≤ D ∧ D ≤ b) (z z₀ : ℂ) :
    ‖p * (D : ℂ) ^ z‖ ≤ ‖p * (D : ℂ) ^ z₀‖ * Real.exp ((|Real.log a| + |Real.log b|) * |z.re - z₀.re|) := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨h1, h2⟩ := h hp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have e : D ^ z.re = D ^ z₀.re * D ^ (z.re - z₀.re) := by
    rw [← Real.rpow_add hD]; congr 1; ring
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hD]
  apply Real.exp_le_exp.2
  calc Real.log D * (z.re - z₀.re) ≤ |Real.log D * (z.re - z₀.re)| := le_abs_self _
    _ = |Real.log D| * |z.re - z₀.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_le hD ha h1 h2) (abs_nonneg _)

theorem re_eq (p : ℂ) {D : ℝ} (hD : 0 < D) (σ u : ℝ) :
    (p * (D : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re = D ^ σ * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hD.ne'), ← Complex.ofReal_cpow hD.le σ,
    show p * (((D ^ σ : ℝ) : ℂ) * (D : ℂ) ^ ((u : ℂ) * Complex.I)) =
      ((D ^ σ : ℝ) : ℂ) * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem msc {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} :
    MeasurableSingletonClass (GA E k) := inferInstance

end LogNormEstimates

theorem log_norm_estimate_of_Q : Q1 → D0 → N3 → C0 → D1 := by
  intro hQ1 hD0 hN3 hC0
  unfold D1 ForMu
  intro E _ _ _ k μ _ hk β hβ S P u z₀ hPc hPinv hP1 hpos hint
  obtain ⟨hDpos, hDmul, hDc, -, hDUU, -⟩ := hD0 E k
  obtain ⟨hG0o, h1G0, hG0inv, -⟩ := hC0 E k S
  obtain ⟨hNP, -, -, hN0⟩ := hN3 E k
  obtain ⟨hνs, hνinv, -⟩ := hNP 0 (by omega)
  obtain ⟨a, b, ha, hab⟩ := hpos
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    simp only [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (by rw [mul_one]; exact h.symm))
  have hG0m : MeasurableSet (G0 (k := k) S) := hG0o.measurableSet
  have hcont : ∀ z : ℂ, Continuous fun g : GA E k => P g * (Dt g : ℂ) ^ z := fun z =>
    hPc.mul ((Complex.continuous_ofReal.comp hDc).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g))
  set L := |Real.log a| + |Real.log b| with hL
  have hL0 : 0 ≤ L := by positivity
  have hdom : ∀ g ∈ G0 (k := k) S, ∀ z : ℂ,
      ‖P g * (Dt g : ℂ) ^ z‖ ≤ ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * |z.re - z₀.re|) := by
    intro g hg z
    exact LogNormEstimates.norm_le (hDpos g) ha (fun hp => ⟨(hab g hg hp).1, (hab g hg hp).2.1⟩) z z₀
  have hintG : ∀ z : ℂ, Integrable (fun g => P g * (Dt g : ℂ) ^ z) ((μ.withDensity β).restrict (G0 S)) := by
    intro z
    refine Integrable.mono' ((hint.norm.mul_const (Real.exp (L * |z.re - z₀.re|))).restrict)
      (hcont z).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hG0m fun g hg => hdom g hg z
  refine ⟨fun z₁ => ?_, fun σ => ?_⟩
  · have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ.withDensity β).restrict (G0 S))
      (F := fun z g => P g * (Dt g : ℂ) ^ z)
      (F' := fun z g => P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ)) (x₀ := z₁)
      (bound := fun g => ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1)) * L) (Metric.ball_mem_nhds z₁ zero_lt_one)
      (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) (hintG z₁)
      ((hcont z₁).mul (Complex.continuous_ofReal.comp (hDc.log fun g => (hDpos g).ne'))).aestronglyMeasurable
      ?_ (((hint.norm.mul_const _).mul_const _).restrict) ?_
    · exact hderiv.2.differentiableAt
    · refine ae_restrict_of_forall_mem hG0m fun g hg z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : P g = 0
      · simp only [hp, zero_mul, norm_zero]; positivity
      have hlog := LogNormEstimates.log_le (hDpos g) ha (hab g hg hp).1 (hab g hg hp).2.1
      have hz' : |z.re - z₀.re| ≤ |z₁.re - z₀.re| + 1 := by
        have h1 : |z.re - z₁.re| ≤ 1 := by
          have := Complex.abs_re_le_norm (z - z₁)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          rw [Complex.sub_re] at this; linarith
        calc |z.re - z₀.re| = |(z.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
          _ ≤ |z.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
          _ ≤ _ := by linarith
      have e1 := hdom g hg z
      have e2 : Real.exp (L * |z.re - z₀.re|) ≤ Real.exp (L * (|z₁.re - z₀.re| + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' hL0)
      calc ‖P g * (Dt g : ℂ) ^ z‖ * |Real.log (Dt g)|
          ≤ (‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1))) * L := by
            apply mul_le_mul _ hlog (abs_nonneg _) (by positivity)
            exact e1.trans (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := rfl
    · refine Filter.Eventually.of_forall fun g z _ => ?_
      have hD := hDpos g
      have h := ((hasDerivAt_id z).const_cpow (c := (Dt g : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hD.ne'))).const_mul (P g)
      have e : P g * ((Dt g : ℂ) ^ id z * Complex.log (Dt g) * 1) =
          P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ) := by
        rw [Complex.ofReal_log hD.le]; simp only [id, mul_one]; ring
      exact h.congr_deriv e
  · set f : GA E k → ℝ := fun g => (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp (hcont _)
    set O : Set (GA E k) := G0 S ∩ {g | 0 < f g} with hO
    have hOo : IsOpen O := hG0o.inter (isOpen_lt continuous_const hfc)
    have hOm : MeasurableSet O := hOo.measurableSet
    have h1O : (1 : GA E k) ∈ O := by
      refine ⟨h1G0, ?_⟩
      show 0 < (P 1 * ((Dt (1 : GA E k) : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)).re
      rw [hD1, Complex.ofReal_one, Complex.one_cpow, mul_one]; exact hP1
    have hOinv : ∀ n g, UU 0 n → (n * g ∈ O ↔ g ∈ O) := by
      intro n g hn
      simp only [hO, hf, Set.mem_inter_iff, Set.mem_setOf_eq, hG0inv n g hn, hPinv n hn g, hDmul, hDUU 0 n hn,
        one_mul]
    haveI : MeasurableSingletonClass (GA E k) := LogNormEstimates.msc
    set_option synthInstance.maxHeartbeats 400000 in
    have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨1, h1O⟩).ne'
    have hβO : μ.withDensity β O ≠ 0 := by
      intro h0
      apply hμO
      have hin : ∀ g, ∫⁻ r, O.indicator 1 (r * g) ∂nuP E k 0 = O.indicator 1 g * nuP E k 0 Set.univ := by
        intro g
        rw [← lintegral_const]
        apply lintegral_congr_ae
        filter_upwards [(hN0 hk).1] with r hr
        by_cases hg : g ∈ O
        · simp [Set.indicator_apply, hg, (hOinv r g hr).2 hg]
        · simp [Set.indicator_apply, hg, mt (hOinv r g hr).1 hg]
      have key := hQ1 (GA E k) μ (Measure.dirac 1) (nuP E k 0) {1} (fun _ => 1) β
        (by rw [Measure.map_dirac' measurable_inv, inv_one]) (by rw [ae_dirac_eq]; exact rfl)
        ⟨measurable_const, fun g => by simp⟩ hβ.1
        (fun g => by
          simp only [lintegral_dirac, mul_one]
          calc ∫⁻ r, β (r⁻¹ * g) ∂nuP E k 0 = ∫⁻ r, β (r * g) ∂(Measure.map (fun h => h⁻¹) (nuP E k 0)) :=
                (lintegral_map (hβ.1.comp (measurable_mul_const g)) measurable_inv).symm
            _ = 1 := by rw [hνinv]; exact hβ.2 g)
        (O.indicator 1) (measurable_one.indicator hOm) (by rintro h rfl g; simp)
      have hw : μ.withDensity (fun _ => (1 : ℝ≥0∞)) = μ := withDensity_one
      rw [hw, lintegral_indicator_one hOm] at key
      rw [key]
      simp_rw [hin]
      rw [lintegral_mul_const _ (measurable_one.indicator hOm), lintegral_indicator_one hOm, h0, zero_mul]
    intro hzero
    have hFi := hintG ((σ : ℂ) + u * Complex.I)
    have hre := integral_re hFi
    rw [hzero] at hre
    simp only [RCLike.re_to_complex, Complex.zero_re] at hre
    have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae (s := G0 S) (μ := μ.withDensity β)
      (f := fun g => (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re)
      (ae_restrict_of_forall_mem hG0m fun g hg => ?_) hFi.re).2 ?_
    · linarith
    · by_cases hp : P g = 0
      · simp [hp]
      show 0 ≤ (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re
      rw [LogNormEstimates.re_eq _ (hDpos g)]
      exact mul_nonneg (Real.rpow_nonneg (hDpos g).le _) (hab g hg hp).2.2
    · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hβO) (measure_mono fun g hg => ⟨?_, hg.1⟩)
      rw [Function.mem_support, LogNormEstimates.re_eq _ (hDpos g)]
      exact (mul_pos (Real.rpow_pos_of_pos (hDpos g) σ) hg.2).ne'

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.MeasureInverseInduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace MeasureInverseInduction

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countGL : Countable (GL (Fin k) E) := by
  haveI : Countable E := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Units.val_injective.countable

theorem blk_ratGL {j : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory j γ) : GlobalTheory j (ratGL E k γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  exact tsum_congr fun γ => lintegral_map hF (measurable_const_mul _)

theorem inv_step (ν : Measure (GA E k)) (hinvν : Measure.map (fun h => h⁻¹) ν = ν) (g : GA E k)
    (hc : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F (g * h * g⁻¹) ∂ν = ∫⁻ h, F h ∂ν)
    (f : GA E k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * h) ∂ν := by
  have hG : Measurable fun x : GA E k => f (g⁻¹ * (g * x * g⁻¹)) :=
    hf.comp ((measurable_const_mul _).comp ((measurable_mul_const _).comp (measurable_const_mul _)))
  calc ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * (g * h⁻¹ * g⁻¹)) ∂ν :=
        lintegral_congr fun h => by congr 1; group
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂Measure.map (fun h => h⁻¹) ν := (lintegral_map hG measurable_inv).symm
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂ν := by rw [hinvν]
    _ = ∫⁻ x, f (g⁻¹ * x) ∂ν := hc (fun y => f (g⁻¹ * y)) (hf.comp (measurable_const_mul _))

def invE (Γ : Set (GL (Fin k) E)) (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) : Γ ≃ Γ where
  toFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  invFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  left_inv γ := Subtype.ext (inv_inv γ.1)
  right_inv γ := Subtype.ext (inv_inv γ.1)

theorem inv_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ)
    (hinvν : Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d)
    (hconj : ∀ γ ∈ Γ, ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (ratGL E k γ * h * (ratGL E k γ)⁻¹) ∂nuD E k d = ∫⁻ h, F h ∂nuD E k d)
    (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc ∫⁻ h, f h ∂Measure.map (fun h => h⁻¹) (nuG Γ d) = ∫⁻ h, f h⁻¹ ∂nuG Γ d :=
        lintegral_map hf measurable_inv
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h)⁻¹ ∂nuD E k d := lint_nuG Γ d _ (hf.comp measurable_inv)
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ.1⁻¹ * h) ∂nuD E k d := tsum_congr fun γ => by
        rw [inv_step _ hinvν _ (hconj γ.1 γ.2) f hf, map_inv (ratGL E k) γ.1]
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d :=
        (invE Γ hΓ).tsum_eq (fun γ : Γ => ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d)
    _ = ∫⁻ h, f h ∂nuG Γ d := (lint_nuG Γ d f hf).symm

theorem sf_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) [SFinite (nuD E k d)] : SFinite (nuG Γ d) := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [nuG]; infer_instance

theorem ae_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (hae : ∀ᵐ u ∂nuD E k d, UU (k - d) u) :
    ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [ae_iff] at hae ⊢
  rw [nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
  intro γ
  rw [(measurableEmbedding_mulLeft (ratGL E k γ)).map_apply]
  exact measure_mono_null (t := {u | ¬ UU (k - d) u})
    (fun u hu hUU => hu ⟨γ.1, u, γ.2, hUU, rfl⟩) hae

theorem nuD_ne_zero (hsf : ∀ d ≤ k, SFinite (nuD E k d)) : ∀ d ≤ k, nuD E k d ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro _ h
    have h1 := congrArg (fun μ : Measure (GA E k) => μ Set.univ) h
    simp [nuD] at h1
  | succ d ih =>
    intro hd h
    haveI := hsf d (by omega)
    have hm : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2 :=
      (((continuous_posU (isNil_blk k _ _)).comp continuous_fst).mul continuous_snd).measurable
    have h3 := (Measure.map_eq_zero_iff hm.aemeasurable).mp h
    have h2 := congrArg (fun μ => μ (vecDomain E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) ×ˢ Set.univ)) h3
    simp only [Measure.prod_prod, vecMeasure_vecDomain, one_mul, Measure.coe_zero, Pi.zero_apply] at h2
    exact ih (by omega) (Measure.measure_univ_eq_zero.mp h2)

variable [_root_.NumberField.IsTotallyComplex E]

theorem main_nuG (hD0 : D0) (hN1 : N1) (Γ : Set (GL (Fin k) E)) (d : ℕ) (hd : d ≤ k)
    (hinv : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hblk : ∀ γ ∈ Γ, GlobalTheory (k - d) γ) :
    SFinite (nuG Γ d) ∧ Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d ∧
      ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  obtain ⟨hsf, hae, hinvν, -, hconj⟩ := hN1 E k d hd
  haveI := hsf
  refine ⟨sf_nuG Γ d, inv_nuG Γ d hinvν (fun γ hγ F hF => ?_) hinv, ae_nuG Γ d hae⟩
  rw [hconj _ (blk_ratGL (hblk γ hγ)) F hF, (hD0 E k).2.2.2.1 γ, inv_one, ENNReal.ofReal_one, one_pow, one_mul]

end MeasureInverseInduction

open MeasureInverseInduction in
set_option synthInstance.maxHeartbeats 400000 in
theorem galois_fixed_adelic_matrices_descend : D0 → N0 → N1 → N3 := by
  intro hD0 hN0 hN1 E _ _ _ k
  have hP : ∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
      ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u := by
    intro m hm
    have hN := hN0 E k (m + 1) (by omega) (by omega)
    have h6 : ∀ γ : GL (Fin k) E, IsMir m γ → IsMir m γ⁻¹ ∧ GlobalTheory (m + 1) γ := by
      simpa only [Nat.add_sub_cancel] using hN.2.2.2.2.2.1
    have e : k - (k - (m + 1)) = m + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | IsMir m γ} (k - (m + 1)) (by omega)
      (fun γ hγ => (h6 γ hγ).1) (fun γ hγ => by rw [e]; exact (h6 γ hγ).2)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hB : ∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
      ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u := by
    intro j hj
    have hinv : ∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹ := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
        subst this
        rw [inv_one]
        exact hγ
      · exact (hN0 E k j hpos hj).2.2.2.1 γ hγ
    have e : k - (k - j) = j := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | GlobalTheory j γ} (k - j) (by omega)
      (fun γ hγ => hinv γ hγ) (fun γ hγ => by rw [e]; exact hγ)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hall : ∀ γ : GL (Fin k) E, γ ∈ {γ : GL (Fin k) E | GlobalTheory k γ} := fun γ i c h =>
    absurd h (not_or.mpr ⟨not_le.mpr i.isLt, not_le.mpr c.isLt⟩)
  have hK : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ) := by
    intro F hF
    rw [nuB, lint_nuG _ _ F hF, Nat.sub_self]
    simp only [nuD, lintegral_dirac, mul_one]
    exact (Equiv.subtypeUnivEquiv hall).tsum_eq (fun γ => F (ratGL E k γ))
  have h4 : 1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0 := by
    intro hk
    obtain ⟨-, -, hae⟩ := hP 0 (by omega)
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
      have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
      rw [hh, this, map_one, one_mul]
      exact ⟨hu.1, hu.2.1, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · intro h0
      haveI : Countable (GL (Fin k) E) := countGL
      have h1 : nuP E k 0 Set.univ = 0 := by simp [h0]
      rw [nuP, nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero] at h1
      have h2 := h1 ⟨1, show IsMir 0 (1 : GL (Fin k) E) from fun i c _ => rfl⟩
      rw [(measurableEmbedding_mulLeft _).map_apply, Set.preimage_univ, Measure.measure_univ_eq_zero] at h2
      exact nuD_ne_zero (fun d hd => (hN1 E k d hd).1) _ (by omega) h2
  exact ⟨hP, hB, hK, h4⟩

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PsiDeterminantFlag
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PsiDeterminantFlag

theorem exists_psiOK {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ χ : AddChar (w.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ := by
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (w.adicCompletion E)
  exact ⟨_, GlobalTheory.CompanionTheory.JSBound.psiOK_of_hasConductor hψ₁⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem dt_fl (hG0 : jumpWindows.G0) (hD0 : D0) (w : Pl E)
    (n : GL (Fin k) (w.adicCompletion E)) (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k)
    (κ : GL (Fin k) (w.adicCompletion E)) (hκ : κ ∈ GLnLocal.integralGL (w.adicCompletion E) k)
    (l : Fin k → ℤ) :
    Dt (fl k w (n * Iwasawa.torusPow (w.adicCompletion E) k l * κ)) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  obtain ⟨_, hmul, _, _, hUU, _, _, _, _, htor, hint⟩ := hD0 E k
  obtain ⟨_, _, hci, hcl, hcl', -⟩ := hG0 E k
  have h1 : Dt (fl k w n) = 1 := by
    obtain ⟨t1, t2, -⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E k w n (fun i j hij => hn.1 hij) hn.2
    exact hUU 0 _ ⟨t1, t2, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
  have h2 : Dt (fl k w κ) = 1 := by
    refine hint _ (hci w κ) fun v => ?_
    by_cases hv : v = w
    · subst hv; rw [hcl]; exact hκ
    · rw [hcl' w v κ hv]; exact one_mem _
  rw [map_mul, map_mul, hmul, hmul, h1, h2, htor, one_mul, mul_one]

end PsiDeterminantFlag

theorem mean_convergence_of : jumpWindows.G0 → D0 → P2 → C0 → C2 → D1 → M0 → LocalHeckeAlgebra → CAUCHY → M1 := by
  intro hG0 hD0 hP2 _ hC2 hD1 hM0 hK8a hC E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hkm hα hα' hD
  have : BorelSpace (GA E k) := ⟨rfl⟩
  obtain ⟨hpos, hmul, hcont, -, hUU, -⟩ := hD0 E k
  obtain ⟨hlaw, hpsN, hUU01, hwhit, -, hgood, -⟩ := hP2 E k ψ hψ
  obtain ⟨β', σ₀', hβ', hM⟩ := hM0 E k μ hk β hβ ψ hψ S m α α' u f φ hD
  have hk1 : k - 1 < k := by omega
  have hWf : Pre ψ 0 (whit ψ (k - 1) f) := hwhit _ hk1 f hD.pre
  have hWφ : Pre ψ 0 (whit ψ (k - 1) φ) := hwhit _ hk1 φ (hgood _ φ hD.good)
  have hPc : Continuous (PW ψ f φ) := hWf.cont.mul (Complex.continuous_conj.comp hWφ.cont)
  have hPu : ∀ n, UU 0 n → ∀ g, PW ψ f φ (n * g) = PW ψ f φ g := by
    intro n hn g
    have h1 := hlaw 0 _ hWf n (hUU01 n hn) g
    have h2 := hlaw 0 _ hWφ n (hUU01 n hn) g
    simp only [PW, h1, h2, map_mul]
    have e : psN ψ n * conj (psN ψ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpsN]; simp
    linear_combination (whit ψ (k - 1) f g * conj (whit ψ (k - 1) φ g)) * e
  have hDtu : ∀ n, UU 0 n → ∀ g, Dt (n * g) = Dt g := fun n hn g => by rw [hmul, hUU 0 n hn, one_mul]
  have hDtm : Measurable fun g : GA E k => (Dt g : ℂ) := Complex.measurable_ofReal.comp hcont.measurable
  have hΦm : ∀ z : ℂ, Measurable fun g => PW ψ f φ g * (Dt g : ℂ) ^ z := fun z =>
    hPc.measurable.mul (hDtm.pow_const z)
  have hΦu : ∀ z : ℂ, ∀ n, UU 0 n → ∀ g,
      PW ψ f φ (n * g) * (Dt (n * g) : ℂ) ^ z = PW ψ f φ g * (Dt g : ℂ) ^ z := by
    intro z n hn g; rw [hPu n hn, hDtu n hn]
  have hχ : ∀ w : Off E S, ∃ χ : AddChar (w.1.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ :=
    fun w => PsiDeterminantFlag.exists_psiOK w.1
  let a' : ℂ → Off E S → (Fin k → ℤ) → ℂ := fun z w l =>
    aLoc α α' w l * (((nq w : ℝ) ^ (-∑ i, l i) : ℝ) : ℂ) ^ z
  have ha0 : ∀ z w, a' z w 0 = 1 := by
    intro z w
    obtain ⟨χ, hχ'⟩ := hχ w
    simp [a', (hK8a E S m k α α' w χ hχ' hk hkm).1]
  have hlawz : ∀ z, LawOff S (fun g => PW ψ f φ g * (Dt g : ℂ) ^ z) (a' z) := by
    intro z w g hg n hn κ hκ l
    simp only [a']
    rw [hD.law w g hg n hn κ hκ l, hmul, PsiDeterminantFlag.dt_fl hG0 hD0 w.1 n hn κ hκ l, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hpos g).le (by positivity)]
    simp only [nq]; ring
  have hI : ∀ s : ℂ, 2 < s.re → σ₀' < (s - ((m : ℂ) - k) / 2).re →
      ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β' =
        (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β') * LS S α α' s := by
    intro s hs hs'
    have hsum := hC2 E k μ hk β' hβ' S _ (a' (s - ((m : ℂ) - k) / 2)) (hΦm _) (hΦu _) (hlawz _) (ha0 _)
      (hM _ hs').1
    obtain ⟨-, hL⟩ := hC E S m k α α' s hkm hα hα' hs
    have e : (fun l : Off E S →₀ (Fin k → ℤ) => ∏ w ∈ l.support, loc (nq w) (α w) (α' w) s (l w)) =
        fun l => ∏ w ∈ l.support, (nq w : ℂ) ^ rhoPair (l w) * a' (s - ((m : ℂ) - k) / 2) w (l w) := by
      funext l
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨χ, hχ'⟩ := hχ w
      exact (((hK8a E S m k α α' w χ hχ' hk hkm).2 (l w)).1 s).symm
    rw [e] at hL
    have hL2 := hL.mul_right (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β')
    rw [mul_comm _ (LS S α α' s)]
    exact hsum.unique hL2
  obtain ⟨hdiff, hnz⟩ := hD1 E k μ hk β' hβ' S (PW ψ f φ) u ((σ₀' + 1 : ℝ) : ℂ) hPc hPu hD.one hD.pos
    (hM _ (by simp)).1
  refine ⟨fun s => ∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β',
    max 2 (σ₀' + ((m : ℝ) - k) / 2), hdiff.comp (differentiable_id.sub_const _), ?_, ?_⟩
  · intro σ
    have e : ((σ : ℂ) + u * Complex.I) - ((m : ℂ) - k) / 2 =
        ((σ - ((m : ℝ) - k) / 2 : ℝ) : ℂ) + u * Complex.I := by push_cast; ring
    dsimp only
    rw [e]
    exact hnz _
  · intro s hs
    have hs2 : 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hre : (s - ((m : ℂ) - k) / 2).re = s.re - ((m : ℝ) - k) / 2 := by simp
    have hs' : σ₀' < (s - ((m : ℂ) - k) / 2).re := by
      rw [hre]; linarith [le_max_right 2 (σ₀' + ((m : ℝ) - k) / 2)]
    have e1 : ∀ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) * (Dt g : ℂ) ^ s =
        sumF f g * conj (φ g) * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) := by
      intro g
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hpos g).ne'), neg_add_eq_sub]
    simp_rw [e1]
    rw [(hM _ hs').2, hI s hs2 hs']

end PositivityTheory.AdelicQuotientData

end
end

