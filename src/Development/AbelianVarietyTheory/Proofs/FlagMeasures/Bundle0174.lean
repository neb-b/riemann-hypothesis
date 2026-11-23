module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquiv
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellDens.ScaledVol

theorem measurePreserving_inv_sqrt_two_smul (r : ℕ) :
    MeasurePreserving (fun y : Fin r → ℂ => (√2 : ℝ)⁻¹ • y) volume
      (((2 : ℝ≥0∞) ^ r) • volume) := by
  have hs : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_addHaar_smul _ hs, hfin, inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num),
    abs_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

theorem volume_image_eq (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F)
    (hL : ∀ v, ‖L v‖ ^ 2 =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2)
    (s : Set ((A × A) × ((Fin r → ℂ) × B))) (hs : MeasurableSet s) :
    volume (L '' s) = 2 ^ r * volume s := by
  have hc : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  let Ψ : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗ[ℝ]
      ((A × A) × ((Fin r → ℂ) × B)) :=
    (WithLp.linearEquiv 2 ℝ _).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (A × A))
        ((WithLp.linearEquiv 2 ℝ _).trans
          (LinearEquiv.prodCongr
            ((WithLp.linearEquiv 2 ℝ (Fin r → ℂ)).trans
              (LinearEquiv.smulOfNeZero ℝ (Fin r → ℂ) (√2 : ℝ)⁻¹ hc))
            (LinearEquiv.refl ℝ B))))
  have hΨ : ∀ x, Ψ x = (x.ofLp.1.ofLp, ((√2 : ℝ)⁻¹ • x.ofLp.2.ofLp.1.ofLp, x.ofLp.2.ofLp.2)) :=
    fun _ => rfl
  let G : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗᵢ[ℝ] F :=
    { Ψ.trans L.toLinearEquiv with
      norm_map' := fun x => by
        change ‖L (Ψ x)‖ = ‖x‖
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hL, hΨ, WithLp.prod_norm_sq_eq_of_L2,
          WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
        simp [norm_smul, mul_pow, Finset.mul_sum, ← mul_assoc, add_assoc] }
  have h0 := (measurePreserving_inv_sqrt_two_smul r).comp
    (GlobalTheory.volume_preserving_ofLp_complex (Fin r))
  haveI : SFinite (((2 : ℝ≥0∞) ^ r) • (volume : Measure (Fin r → ℂ))) := inferInstance
  have h1 := (h0.prod (MeasurePreserving.id (volume : Measure B))).comp
    (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin r)) B)
  have h2 := ((WithLp.volume_preserving_ofLp A A).prod h1).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (A × A)) (WithLp 2 (EuclideanSpace ℂ (Fin r) × B)))
  have h3 := h2.measure_preimage hs.nullMeasurableSet
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h3
  have hm : MeasurableSet (L '' s) :=
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  rw [← h3, ← G.measurePreserving.measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  change L (Ψ x) ∈ L '' s ↔ Ψ x ∈ s
  exact L.injective.mem_set_image

end GlobalTheory.CellDens.ScaledVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightLeOfMemWtSpan
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.FilGrowth

def wtSpan {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (R : ℝ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ ν : Fin n → ℝ, IsWeight E ν z ∧ ∀ a, |ν a| ≤ R}

section Alg
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V}

theorem isWeight_step (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z) (a b : Fin n) :
    IsWeight E (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b z) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T z) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hz c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a
  · subst h1
    by_cases h2 : b = c
    · subst h2; simp
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h2, h3, add_smul, add_comm]
  · by_cases h2 : b = c
    · subst h2
      simp [h1, sub_smul]
      abel
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h1, h2, h3]

theorem exists_isWeight_word (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z)
    (w : List (Fin n × Fin n)) : ∃ ν' : Fin n → ℝ, IsWeight E ν' (ew E w z) := by
  induction w with
  | nil => exact ⟨ν, by simpa [ew] using hz⟩
  | cons p w ih =>
    obtain ⟨ν', h⟩ := ih
    exact ⟨_, by simpa [ew] using isWeight_step hE h p.1 p.2⟩

theorem wtSpan_mono {R R' : ℝ} (h : R ≤ R') : wtSpan E R ≤ wtSpan E R' :=
  Submodule.span_mono fun _ ⟨ν, h1, h2⟩ => ⟨ν, h1, fun a => (h2 a).trans h⟩

theorem step_mem_wtSpan (hE : GlRel E) {R : ℝ} (a b : Fin n) {z : V} (hz : z ∈ wtSpan E R) :
    E a b z ∈ wtSpan E (R + 1) := by
  have : wtSpan E R ≤ (wtSpan E (R + 1)).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨ν, h1, h2⟩
    refine Submodule.subset_span ⟨_, isWeight_step hE h1 a b, fun c => ?_⟩
    have := abs_le.1 (h2 c)
    rw [abs_le]
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  exact this hz

theorem word_mem_wtSpan (hE : GlRel E) {R : ℝ} (w : List (Fin n × Fin n)) {z : V}
    (hz : z ∈ wtSpan E R) : ew E w z ∈ wtSpan E (R + w.length) := by
  induction w with
  | nil => simpa [ew] using hz
  | cons p w ih =>
    have := step_mem_wtSpan hE p.1 p.2 ih
    simpa [ew, add_assoc] using this

end Alg

section Inner
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ V}

theorem weight_le_of_mem_wtSpan (hU : KUnit ε E) {R : ℝ} {μ : Fin n → ℝ} {y : V}
    (hy : y ∈ wtSpan E R) (hy0 : y ≠ 0) (hμ : IsWeight E μ y) (a : Fin n) : |μ a| ≤ R := by
  by_contra hlt
  have : wtSpan E R ≤ LinearMap.ker (innerₛₗ ℂ y) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨ν, h1, h2⟩
    have hne : μ ≠ ν := by
      rintro rfl
      exact hlt (h2 a)
    exact kWtOrth V n ε E μ ν y z hU hμ h1 hne
  have h0 : ⟪y, y⟫_ℂ = 0 := this hy
  exact hy0 (inner_self_eq_zero.1 h0)

theorem kSpan_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) : kSpan ε E u ≤ wtSpan E (Real.sqrt (ckv ε μ)) := by
  have hl := (kLow V n ε E μ u (glRel_kRel ε E hE) hu).1
  rw [hl]
  refine Submodule.span_le.2 ?_
  rintro y ⟨w, hw, rfl⟩
  have hmem : ew E w u ∈ kSpan ε E u := by
    rw [hl]; exact Submodule.subset_span ⟨w, hw, rfl⟩
  by_cases h0 : ew E w u = 0
  · rw [h0]; exact Submodule.zero_mem _
  obtain ⟨ν, hν⟩ := exists_isWeight_word hE hu.1 w
  have hb := kWtBound V n ε E μ ν u _ (glRel_kRel ε E hE) hU hu hmem h0 hν
  refine Submodule.subset_span ⟨ν, hν, fun a => ?_⟩
  apply Real.abs_le_sqrt
  refine le_trans ?_ hb
  unfold Formalism.REAL.nsq Formalism.REAL.dot
  rw [sq]
  exact Finset.single_le_sum (f := fun a => ν a * ν a) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ a)

theorem pfil_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) (j : ℕ) : pfil ε E u j ≤ wtSpan E (Real.sqrt (ckv ε μ) + j) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨w, hw, -, y, hy, rfl⟩
  refine wtSpan_mono ?_ (word_mem_wtSpan hE w (kSpan_le_wtSpan hE hU hu hy))
  have : (w.length : ℝ) ≤ j := by exact_mod_cast hw
  linarith

end Inner

theorem uGrowth : UGrowth := by
  intro V _ _ n ε E μ c u hE hU hu hc hfd j x hx
  have hK := isUnitary_kUnit ε E hU
  obtain ⟨-, -, hst, -, hcyc, -, hfin⟩ := pfilFacts V n ε E u hE
  have hb := kCasBound V n ε E (pfil ε E u j) (Real.sqrt (ckv ε μ) + j) (hfin hfd j)
    (glRel_kRel ε E hE) hK (hst j) (by positivity)
    (fun ν y hy hy0 hν a => weight_le_of_mem_wtSpan hK (pfil_le_wtSpan hE hK hu j hy) hy0 hν a) x hx
  have hcas := casOnCyc V n E c u hE hc x (hcyc j hx)
  have hs := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hU)
  rw [Complex.ofReal_re, LinearMap.sub_apply, hcas, two_smul, LinearMap.add_apply, inner_sub_right,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at hs
  have h2 : ((c : ℂ) * ((‖x‖ : ℂ)) ^ 2).re = c * ‖x‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.sub_re, Complex.add_re] at hs
  have h3 : ((c : ℂ) * (RCLike.ofReal ‖x‖ : ℂ) ^ 2).re = c * ‖x‖ ^ 2 := h2
  rw [h3] at hs
  rw [hs]
  have h4 : -c * ‖x‖ ^ 2 ≤ |c| * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_le_abs c) (by positivity)
  linarith

end GlobalTheory.FilGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaWithCutoffSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

private theorem lintegral_eq_lintegral_weight_mul_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (φ : G → ENNReal) (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂μ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
  calc ∫⁻ y, φ y ∂μ = ∫⁻ y, (∫⁻ m, β (m⁻¹ * y) ∂ν) * φ y ∂μ := by
          simp only [hone, one_mul]
    _ = ∫⁻ y, ∫⁻ m, β (m⁻¹ * y) * φ y ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
          exact (lintegral_mul_const _ hb).symm
    _ = ∫⁻ m, ∫⁻ y, β (m⁻¹ * y) * φ y ∂μ ∂ν := by
          have hm : Measurable (fun p : G × G => β (p.2⁻¹ * p.1) * φ p.1) :=
            (hβ.comp (measurable_snd.inv.mul measurable_fst)).mul (hφ.comp measurable_fst)
          exact lintegral_lintegral_swap (f := fun y m => β (m⁻¹ * y) * φ y) hm.aemeasurable
    _ = ∫⁻ m, ∫⁻ y, β y * φ (m * y) ∂μ ∂ν := by
          refine lintegral_congr (fun m => ?_)
          have h := lintegral_mul_left_eq_self (μ := μ) (fun y => β (m⁻¹ * y) * φ y) m
          simp only [inv_mul_cancel_left] at h
          exact h.symm
    _ = ∫⁻ y, ∫⁻ m, β y * φ (m * y) ∂ν ∂μ := by
          have hm : Measurable (fun p : G × G => β p.2 * φ (p.1 * p.2)) :=
            (hβ.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
          exact lintegral_lintegral_swap (f := fun m y => β y * φ (m * y)) hm.aemeasurable
    _ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => φ (m * y)) := hφ.comp (measurable_mul_const y)
          exact lintegral_const_mul _ hb

private theorem integrable_and_integral_eq_of_lintegral_weight_one {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hfin : ∀ y, β y ≠ ⊤) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (g : G → ℂ) (hg : Measurable g) (hgi : Integrable g μ) :
    Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ ∧
      ∫ y, g y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ := by
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  have hgl : ∫⁻ y, ‖g y‖ₑ ∂μ < ⊤ := hgi.hasFiniteIntegral
  have hnorm : ∀ y (z : ℂ), ‖((β y).toReal : ℂ) * z‖ₑ = β y * ‖z‖ₑ := by
    intro y z
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
  have hHm : Measurable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) :=
    (Complex.measurable_ofReal.comp (hβ.comp measurable_snd).ennreal_toReal).mul
      (hg.comp (measurable_fst.mul measurable_snd))
  have hHi : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) (ν.prod μ) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β p.2).toReal : ℂ) * g (p.1 * p.2)‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hHm.enorm.aemeasurable]
    simp only [hnorm]
    have h2 : ∀ y, ∫⁻ m, β y * ‖g (m * y)‖ₑ ∂ν = β y * ∫⁻ m, ‖g (m * y)‖ₑ ∂ν := fun y =>
      lintegral_const_mul _ (hg.enorm.comp (measurable_mul_const y))
    simp only [h2]
    rw [← hkey _ hg.enorm]
    exact hgl
  have heq : ∀ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν = ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν :=
    fun y => integral_const_mul _ _
  have hint0 : Integrable (fun y => ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν) μ :=
    hHi.integral_prod_right
  have hint : Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ :=
    hint0.congr (ae_of_all _ heq)
  refine ⟨hint, ?_⟩
  have hKm : Measurable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) :=
    (Complex.measurable_ofReal.comp
      (hβ.comp (measurable_fst.inv.mul measurable_snd)).ennreal_toReal).mul (hg.comp measurable_snd)
  have hKi : Integrable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) (ν.prod μ) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hKm.enorm.aemeasurable]
    simp only [hnorm]
    have h3 : ∀ y, ∫⁻ m, β (m⁻¹ * y) * ‖g y‖ₑ ∂ν = ‖g y‖ₑ := by
      intro y
      have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
      rw [lintegral_mul_const _ hb, hone, one_mul]
    simp only [h3]
    exact hgl
  have hβone : ∀ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν = 1 := by
    intro y
    have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
    rw [integral_complex_ofReal, integral_toReal hb.aemeasurable (ae_of_all _ fun m => (hfin _).lt_top),
      hone, ENNReal.toReal_one, Complex.ofReal_one]
  calc ∫ y, g y ∂μ = ∫ y, (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show g y = (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y
        rw [hβone y, one_mul]
    _ = ∫ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ m, ∫ y, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂μ ∂ν :=
        (integral_prod_symm _ hKi).symm.trans (integral_prod _ hKi)
    _ = ∫ m, ∫ y, ((β y).toReal : ℂ) * g (m * y) ∂μ ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun m => ?_)
        have h := integral_mul_left_eq_self (μ := μ) (fun y => ((β (m⁻¹ * y)).toReal : ℂ) * g y) m
        simp only [inv_mul_cancel_left] at h
        exact h.symm
    _ = ∫ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν ∂μ :=
        (integral_prod _ hHi).symm.trans (integral_prod_symm _ hHi)
    _ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ :=
        integral_congr_ae (ae_of_all _ heq)

theorem weil_formula_cutoff : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N ν _hN hH β hβ hfin hone
  have hH' := hH
  unfold IsHaarSub at hH'
  haveI : IsFiniteMeasureOnCompacts ν := hH'.2.1
  haveI : SigmaFinite ν := inferInstance
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  refine ⟨hkey, fun f hf => ?_⟩
  have hgm : Measurable (hf.aestronglyMeasurable.mk f) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  obtain ⟨hgi, hgeq⟩ := integrable_and_integral_eq_of_lintegral_weight_one μ ν β hβ hfin hone _ hgm (hf.congr hfg)
  have hEm : MeasurableSet (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) :=
    measurableSet_toMeasurable _ _
  have hE0 : μ (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hfg
  have hsub : {y | f y ≠ hf.aestronglyMeasurable.mk f y} ⊆
      toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y} := subset_toMeasurable _ _
  have hind : Measurable ((toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal)) := measurable_one.indicator hEm
  have h0 := hkey _ hind
  rw [lintegral_indicator_one hEm, hE0] at h0
  have hIm : Measurable (fun y => β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal) (m * y) ∂ν) :=
    hβ.mul (hind.comp measurable_mul).lintegral_prod_left'
  have hae := (lintegral_eq_zero_iff' hIm.aemeasurable).mp h0.symm
  have hcong : (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) =ᵐ[μ]
      (fun y => ((β y).toReal : ℂ) * ∫ m, hf.aestronglyMeasurable.mk f (m * y) ∂ν) := by
    filter_upwards [hae] with y hy
    have hy' : β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
        (1 : G → ENNReal) (m * y) ∂ν = 0 := hy
    rcases mul_eq_zero.mp hy' with hb | hI
    · simp [hb]
    · congr 1
      have hmy : Measurable (fun m => (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
          (1 : G → ENNReal) (m * y)) := hind.comp (measurable_mul_const y)
      have hae2 := (lintegral_eq_zero_iff hmy).mp hI
      refine integral_congr_ae ?_
      filter_upwards [hae2] with m hm
      by_contra hne
      have hmE := hsub hne
      simp [Set.indicator_of_mem hmE] at hm
  refine ⟨hgi.congr hcong.symm, ?_⟩
  rw [integral_congr_ae hfg, hgeq, integral_congr_ae hcong]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
section
open MeasureTheory GlobalTheory.Dec

namespace GlobalTheory.Dec

theorem integral_mul_eq_zero_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤) (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (F φ : G → ℂ) (hF : Measurable F) (hφ : Measurable φ) (hinv : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y)
    (hint : Integrable (fun y => F y * φ y) μ) (h0 : ∀ y, ∫ m, φ (m * y) ∂ν = 0) :
    ∫ y, F y * φ y ∂μ = 0 := by
  set f : G × G → ℂ := fun p => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * (F p.2 * φ p.2) with hf_def
  have hβm : Measurable fun p : G × G => β (p.1⁻¹ * p.2) :=
    hβ.comp (measurable_fst.inv.mul measurable_snd)
  have hfm : Measurable f :=
    (Complex.measurable_ofReal.comp hβm.ennreal_toReal).mul
      ((hF.comp measurable_snd).mul (hφ.comp measurable_snd))

  have hβy : ∀ y, Measurable fun m : G => β (m⁻¹ * y) := fun y =>
    hβ.comp (measurable_inv.mul_const y)
  have hfib : ∀ y, ∫ m, (β (m⁻¹ * y)).toReal ∂ν = 1 := by
    intro y
    rw [integral_toReal (hβy y).aemeasurable (Filter.Eventually.of_forall fun m => (hβt _).lt_top),
      hβ1 y, ENNReal.toReal_one]
  have hfibI : ∀ y, Integrable (fun m => (β (m⁻¹ * y)).toReal) ν := fun y =>
    integrable_toReal_of_lintegral_ne_top (hβy y).aemeasurable (by rw [hβ1 y]; exact ENNReal.one_ne_top)

  have hA : ∫ y, F y * φ y ∂μ = ∫ y, ∫ m, f (m, y) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    rw [integral_mul_const, integral_complex_ofReal, hfib y]
    simp

  have hfI : Integrable f (ν.prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · simp only [hf_def]
      exact (hfibI y).ofReal.mul_const _
    · have hn : (fun y => ∫ m, ‖f (m, y)‖ ∂ν) = fun y => ‖F y * φ y‖ := by
        funext y
        simp only [hf_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, ENNReal.abs_toReal]
        rw [integral_mul_const, hfib y, one_mul]
      rw [hn]
      exact hint.norm

  have hmp : MeasurePreserving (fun p : G × G => (p.1, p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_mul ν μ
  have hemb : MeasurableEmbedding (fun p : G × G => (p.1, p.1 * p.2)) :=
    (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hae : ∀ᵐ p ∂(ν.prod μ),
      f (p.1, p.1 * p.2) = ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) := by
    have h1 : ∀ᵐ p ∂(ν.prod μ), ∀ y, F (p.1 * y) = F y :=
      Measure.quasiMeasurePreserving_fst.ae hinv
    filter_upwards [h1] with p hp
    simp only [hf_def, inv_mul_cancel_left, hp]
  have hgI : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)))
      (ν.prod μ) :=
    ((hmp.integrable_comp_emb hemb).2 hfI).congr hae
  calc ∫ y, F y * φ y ∂μ
      = ∫ p, ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) ∂(ν.prod μ) := by
        rw [hA, ← integral_prod_symm f hfI, ← hmp.integral_comp hemb f]
        exact integral_congr_ae hae
    _ = ∫ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν ∂μ := integral_prod_symm _ hgI
    _ = 0 := by
        have hz : ∀ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν = 0 := by
          intro z
          simp_rw [← mul_assoc]
          rw [integral_const_mul, h0 z, mul_zero]
        simp only [hz, integral_zero]

theorem weilVanish : WeilVanish := by
  unfold WeilVanish
  intro G _ _ _ _ _ _ _ _ μ _ N ν hN hν F φ hF hφ hinv hint h0
  obtain ⟨β, hβ, hβt, hβ1⟩ := exists_measurable_cutoff_fibre_integral_one G N ν hN hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hN' : ∀ᵐ m ∂ν, m ∈ (N : Set G) := mem_ae_iff.2 hν.2.2.1
  have hae : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y := hN'.mono fun m hm y => hinv m hm y
  exact integral_mul_eq_zero_of_cutoff μ ν β hβ hβt hβ1 F φ hF hφ hae hint h0

end GlobalTheory.Dec
end

