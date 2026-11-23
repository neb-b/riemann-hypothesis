module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarLintegralMulRightLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2Bound
section
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.QuotLocInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

open MeasureTheory Set in
open scoped ENNReal in
private theorem lintegral_compact_le_mul_lintegral_fundamentalDomain (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (C : Set G) (hC : IsCompact C) (n : ℝ)
    (hn : ∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n)
    (g : G → ℝ≥0∞) (hg : Measurable g) (hinv : ∀ (γ : Γ) x, g (γ • x) = g x) :
    ∫⁻ x in C, g x ∂μ ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, g x ∂μ := by
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hcount : ∀ x : G, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) ≤ ENNReal.ofReal n := by
    intro x
    have hS : ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) =
        ∑' γ : Γ, {γ : Γ | (γ : G) * x ∈ C}.indicator 1 γ := rfl
    rw [hS, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    obtain ⟨hfin, hle⟩ := hn x
    have hE : ({γ : Γ | (γ : G) * x ∈ C}).encard ≤
        (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞) := by
      rw [hfin.cast_ncard_eq, ← Subtype.val_injective.encard_image]
      apply Set.encard_le_encard
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    calc ((({γ : Γ | (γ : G) * x ∈ C}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.mpr hE
      _ = (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal n := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ x in C, g x ∂μ = ∫⁻ x, C.indicator g x ∂μ := (lintegral_indicator hCm _).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator g (γ⁻¹ • x) ∂μ := h𝓕.lintegral_eq_tsum' _
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        congr 1; funext γ; congr 1; funext x
        by_cases hx : γ⁻¹ • x ∈ C <;> simp [hx, hinv]
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact (((measurable_one.indicator hCm).comp (measurable_const_smul _)).mul hg).aemeasurable
    _ = ∫⁻ x in 𝓕, (∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x)) * g x ∂μ := by
        congr 1; funext x
        rw [ENNReal.tsum_mul_right]
        congr 1
        exact (Equiv.inv Γ).tsum_eq (fun γ => C.indicator (1 : G → ℝ≥0∞) (γ • x))
    _ ≤ ∫⁻ x in 𝓕, ENNReal.ofReal n * g x ∂μ :=
        lintegral_mono fun x => by gcongr ?_ * _; exact hcount x
    _ = _ := lintegral_const_mul _ hg


open MeasureTheory Set in
open scoped ENNReal in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G} in
theorem _root_.GlobalTheory.QuotLocInt.integrableOn_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ,
    (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) →
    ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))),
      IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧
        ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  intro G _ _ _ _ _ _ μ _ Γ _ 𝓕 h𝓕 C hC n hn
  refine ⟨(ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ)).toReal, fun F => ?_⟩
  have hπ : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := fun _ hs => hs
  have hF := Lp.stronglyMeasurable F
  have hf : StronglyMeasurable fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x) :=
    hF.comp_measurable hπ
  have hL2 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 2 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hf.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (Lp.aestronglyMeasurable F)]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ x in C, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_compact_le_mul_lintegral_fundamentalDomain G μ Γ 𝓕 h𝓕 C hC n hn _
            ((hF.measurable.eNorm.pow_const _).comp hπ) fun γ x => by
              rw [show Quotient.mk (QuotientGroup.rightRel Γ) (γ • x) = Quotient.mk _ x from
                Quotient.sound (QuotientGroup.rightRel_apply.2 (by simp [Subgroup.smul_def, mul_inv_rev]))]
      _ = _ := by rw [lintegral_map (hF.measurable.eNorm.pow_const _) hπ]
  have hL1 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 1 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf.aestronglyMeasurable).trans ?_
    rw [Measure.restrict_apply_univ]
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [show (1 / 1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    calc _ ≤ ENNReal.ofReal n ^ (1/2 : ℝ) *
          eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) *
            μ C ^ (1/2 : ℝ) := by gcongr
      _ = _ := by ring
  have hfin : ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
      eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) < ⊤ := by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) (Lp.eLpNorm_lt_top F)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.measure_lt_top.ne
  refine ⟨memLp_one_iff_integrable.1 (hL1.trans_lt hfin), ?_⟩
  rw [integral_norm_eq_lintegral_eNorm hf.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin.ne hL1

end GlobalTheory.QuotLocInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GoodEtale

variable {R C O G : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Group G]

def galMap (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) : O ⊗[R] C →ₐ[O] (G → O) :=
  Pi.algHom O (fun _ => O) fun g =>
    Algebra.TensorProduct.lift (AlgHom.id O O) (σ.comp (act g).toAlgHom) (fun _ _ => Commute.all _ _)

@[simp] theorem galMap_tmul (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) (o : O) (c : C) (g : G) :
    galMap act σ (o ⊗ₜ c) g = o * σ (act g c) := by
  simp [galMap]

def galElt (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C) (h : G) : O ⊗[R] C :=
  ∑ i, σ (x i) ⊗ₜ act h⁻¹ (y i)

theorem galMap_galElt [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C)
    (b : R) (hxy : ∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) (h : G) :
    galMap act σ (galElt act σ x y h) = Pi.single h (algebraMap R O b) := by
  funext g
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [galElt, map_sum, Finset.sum_apply, galMap_tmul]
  have : ∀ i, σ (x i) * σ (act g (act h⁻¹ (y i))) = σ (x i * act (g * h⁻¹) (y i)) := by
    intro i; simp [map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [this, ← map_sum, hxy]
  by_cases hg : g = h
  · subst hg; simp
  · have : g * h⁻¹ ≠ 1 := fun e => hg (mul_inv_eq_one.mp e)
    simp [this, hg]

end GlobalTheory.GoodEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphismsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticeRationalSpanInclusions
section
open NumberField

namespace GlobalTheory

theorem differentIdeal_int_le_differentIdeal (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] :
    differentIdeal ℤ (𝓞 K') ≤ differentIdeal (𝓞 K) (𝓞 K') := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 K')]
  exact Ideal.mul_le_left

theorem span_rational_le_span_and_different_smul_le :
    ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  intro K K' L _ _ _ _ _ _ _ _ _ n M hM
  set φ : (Fin n → K') → (Fin n → L) := fun x i => algebraMap K' L (x i) with hφ
  set P := Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) with hP
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  ·
    have himg : ∀ y ∈ Submodule.span (𝓞 K') {y : Fin n → K' | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K K' (y0 i)}, φ y ∈ P := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨hyM, y0, rfl⟩ := hy
        exact Submodule.subset_span ⟨y0, hyM, rfl⟩
      | zero =>
        have h0 : φ 0 = 0 := by funext i; simp [hφ]
        rw [h0]; exact P.zero_mem
      | add a b _ _ ha hb =>
        have : φ (a + b) = φ a + φ b := by funext i; simp [hφ]
        rw [this]; exact P.add_mem ha hb
      | smul c a _ ha =>
        have : φ (c • a) = algebraMap (𝓞 K') (𝓞 L) c • φ a := by
          funext i
          change algebraMap K' L ((c : K') * a i) = ((algebraMap (𝓞 K') (𝓞 L) c : 𝓞 L) : L) * φ a i
          rw [map_mul]; rfl
        rw [this]; exact P.smul_mem _ ha
    rw [Ideal.map, Submodule.span_smul_span, Submodule.span_le]
    intro z hz
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul.mp hz
    have hdK : d ∈ differentIdeal (𝓞 K) (𝓞 K') := differentIdeal_int_le_differentIdeal K K' hd
    have hmem := differentIdeal_smul_mem_span_rational K K' n M hM d hdK x hx
    have h := himg _ hmem
    have : φ (d • x) = algebraMap (𝓞 K') (𝓞 L) d • φ x := by
      funext i
      change algebraMap K' L ((d : K') * x i) = ((algebraMap (𝓞 K') (𝓞 L) d : 𝓞 L) : L) * φ x i
      rw [map_mul]; rfl
    rw [this] at h
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenIntegerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer : ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
  (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
    (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
  (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  first | exact @GlobalTheory.gammaℝ_functional_constant_even | exact GlobalTheory.gammaℝ_functional_constant_even | (intros; apply GlobalTheory.gammaℝ_functional_constant_even <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianConvolutionSeriesCoefficientDescFactoria
section
open MeasureTheory Filter Topology

namespace GlobalTheory.TermEst

lemma pointwise (b c θ α s t H : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ) (hα : 0 < α)
    (hk : c * θ ^ 2 ≤ α * (b + c)) (hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (i m : ℕ) :
    (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m)) ≤
      θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by
  have hθ0 : 0 < θ := by linarith
  have e1 : (2 * c * θ * s * t) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * c * θ * s * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have e2 : 2 * c * θ * s * t ≤ c * α * t ^ 2 + (b + c) * s ^ 2 := by
    have q1 : 0 ≤ c * (α * t - θ * s) ^ 2 := by positivity
    have q2 : c * θ ^ 2 * s ^ 2 ≤ α * (b + c) * s ^ 2 := by
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    have q3 : α * (2 * c * θ * s * t) ≤ α * (c * α * t ^ 2 + (b + c) * s ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left q3 hα
  have e3 : Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t) ≤ Real.exp (c * α * t ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hm : (0 : ℝ) < m.factorial := by positivity
  calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m))
      = ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * ((2 * c * θ * s * t) ^ m / (m.factorial : ℝ))) := by
        rw [inv_pow]; field_simp; ring
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t)) := by gcongr
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * Real.exp (c * α * t ^ 2) := by gcongr
    _ = θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by ring

lemma norm_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ) (a : E) :
    ‖GlobalTheory.ConvSeries.wt b c h a‖ = Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ := by
  simp only [GlobalTheory.ConvSeries.wt, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [mul_comm (Real.exp _) ‖h a‖, mul_assoc, ← Real.exp_add]
  ring_nf

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c θ α : ℝ), 0 < c → 1 ≤ θ → 0 < α → c * θ ^ 2 ≤ α * (b + c) →
    ∀ (h : SchwartzMap E ℂ) (j i : ℕ) (y : E),
    (2 * c) ^ j / (j.factorial : ℝ) * (j.descFactorial i : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) *
      ‖y‖ ^ (j - i) ≤ θ⁻¹ ^ (j - i) * Real.exp (c * α * ‖y‖ ^ 2) * ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ := by
  intro E _ _ _ _ _ b c θ α hc hθ hα hk h j i y
  rcases lt_or_ge j i with hji | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hji, Nat.cast_zero, mul_zero, zero_mul, zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg fun a => by positivity)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_sub_cancel_left]
    have hK : (2 * c) ^ (i + m) / ((i + m).factorial : ℝ) * ((i + m).descFactorial i : ℝ) =
        (2 * c) ^ (i + m) / (m.factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (Nat.le_add_right i m)
      rw [Nat.add_sub_cancel_left] at this
      have h1 : ((i + m).factorial : ℝ) = (m.factorial : ℝ) * ((i + m).descFactorial i : ℝ) := by
        exact_mod_cast this.symm
      have h2 : (0 : ℝ) < m.factorial := by positivity
      have h3 : (0 : ℝ) < ((i + m).descFactorial i : ℝ) := by
        have : (0:ℝ) < ((i + m).factorial : ℝ) := by positivity
        rw [h1] at this
        exact pos_of_mul_pos_right this h2.le
      rw [h1]; field_simp
    rw [hK]
    have hint : Integrable (fun a : E => (2 * c * ‖a‖) ^ i * ‖h a‖) := by
      have := (h.integrable_pow_mul volume i).const_mul ((2 * c) ^ i)
      refine this.congr (Eventually.of_forall fun a => ?_)
      simp only [mul_pow]; ring
    calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ (i + m)) * ‖y‖ ^ m
        = ∫ a, (2 * c) ^ (i + m) / (m.factorial : ℝ) * ‖y‖ ^ m *
            (Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ * ‖a‖ ^ (i + m)) := by
          rw [integral_const_mul]; simp only [norm_wt]; ring
      _ ≤ ∫ a, θ⁻¹ ^ m * Real.exp (c * α * ‖y‖ ^ 2) * ((2 * c * ‖a‖) ^ i * ‖h a‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun a => by positivity)
            (hint.const_mul _) (Eventually.of_forall fun a => ?_)
          exact pointwise b c θ α ‖a‖ ‖y‖ ‖h a‖ hc hθ hα hk (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) i m
      _ = _ := integral_const_mul _ _

end GlobalTheory.TermEst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianIteratedFDerivWeightedExpBounded
section
open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.GaussDerivBound

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add' (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le' (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le_one_add' i x
        · exact norm_iteratedFDeriv_id_le_one_add' (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_rexp' (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp' (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

theorem weighted_bound : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  intro E _ _ c α hc hα k m
  set B : E →L[ℝ] E →L[ℝ] ℝ := (-c) • innerSL ℝ with hBdef
  have hBy : ∀ y : E, B y y = -(c * ‖y‖ ^ 2) := fun y => by
    simp [hBdef, real_inner_self_eq_norm_sq]
    left
    first | exact real_inner_self_eq_norm_sq y | simp [innerSL_apply, real_inner_self_eq_norm_sq] | rfl
  have hfun : (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) =
      Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y) := by
    funext y
    simp only [Function.comp_apply, Complex.ofRealLI_apply, hBy, Complex.ofReal_exp, Complex.ofReal_neg]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  have hc' : 0 < c * (1 - α) := mul_pos hc (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp' (c * (1 - α)) hc' (k + 2 * m)
  refine ⟨m ! * (2 * (‖B‖ + 1)) ^ m * C, fun x => ?_⟩
  have hn : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [hfun, LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp' i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le' B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  rw [hBy x] at hfb
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  have hexp : Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2) =
      Real.exp (-(c * (1 - α) * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (Real.exp ∘ fun y : E => B y y) x‖ * Real.exp (c * α * ‖x‖ ^ 2)
      ≤ (1 + ‖x‖) ^ k * (m ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m) *
          Real.exp (c * α * ‖x‖ ^ 2) := by
        gcongr
        linarith
    _ = m ! * (2 * (‖B‖ + 1)) ^ m * ((1 + ‖x‖) ^ (k + 2 * m) *
          (Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m = (2 * (‖B‖ + 1)) ^ m * (1 + ‖x‖) ^ (2 * m) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ m ! * (2 * (‖B‖ + 1)) ^ m * C := by
        rw [hexp]
        gcongr
        exact hC ‖x‖ hx0

end GlobalTheory.GaussDerivBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetNeZeroOfKerOrthStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_ker_orth' : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A) → (∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) → (∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) → (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  first | exact @GlobalTheory.gram_det_ne_zero_of_ker_orth | exact GlobalTheory.gram_det_ne_zero_of_ker_orth | (intros; apply GlobalTheory.gram_det_ne_zero_of_ker_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  first | exact @GlobalTheory.gram_posSemidef_of_int_form | exact GlobalTheory.gram_posSemidef_of_int_form | (intros; apply GlobalTheory.gram_posSemidef_of_int_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarLintegralMulRightLeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lintegral_mul_right_le_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal, Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.haar_lintegral_mul_right_le | exact GlobalTheory.haar_lintegral_mul_right_le | (intros; apply GlobalTheory.haar_lintegral_mul_right_le <;> assumption)
end

