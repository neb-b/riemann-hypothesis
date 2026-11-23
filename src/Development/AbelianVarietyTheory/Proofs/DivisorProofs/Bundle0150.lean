module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegral
section
open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

open GlobalTheory.ConvSeries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_cexp_neg_ofReal (x : ℝ) : ‖Complex.exp (-((x : ℝ) : ℂ))‖ = Real.exp (-x) := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

lemma norm_wt_le (b c : ℝ) (h : SchwartzMap E ℂ) (a : E) :
    ‖wt b c h a‖ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) := by
  unfold wt
  rw [norm_mul, norm_mul, norm_cexp_neg_ofReal, norm_cexp_neg_ofReal]
  have h1 := SchwartzMap.norm_le_seminorm ℝ h a
  have hs : Real.exp (-((b + c) * ‖a‖ ^ 2)) =
      Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hs]
  calc Real.exp (-(b * ‖a‖ ^ 2)) * ‖h a‖ * Real.exp (-(c * ‖a‖ ^ 2))
      = ‖h a‖ * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) := by ring
    _ ≤ SchwartzMap.seminorm ℝ 0 0 h * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

lemma continuous_wt (b c : ℝ) (h : SchwartzMap E ℂ) : Continuous (wt b c h) := by
  have hc : Continuous (h : E → ℂ) := h.continuous
  unfold wt
  fun_prop

lemma norm_innerC_le (a : E) : ‖innerC a‖ ≤ ‖a‖ := by
  unfold innerC
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [Complex.ofRealCLM_norm, one_mul, innerSL_apply_norm]

lemma norm_powForm_le (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ * ‖a‖ ^ k := by
  unfold powForm
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact norm_innerC_le a

lemma continuous_powForm (k : ℕ) : Continuous (fun a : E => powForm k a) := by
  have hi : Continuous (fun a : E => innerC a) := by
    unfold innerC
    exact continuous_const.clm_comp (innerSL ℝ (E := E)).continuous
  have hf : (fun a : E => powForm k a) = fun a =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ (fun _ => innerC a))
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ) := by
    funext a; rfl
  rw [hf]
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ).cont.comp (continuous_pi fun _ => hi)).clm_apply
    continuous_const

lemma pow_mul_exp_le {β : ℝ} (hβ : 0 < β) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x ^ 2)) ≤
      k.factorial * Real.exp (1 / (2 * β)) * Real.exp (-(β / 2 * x ^ 2)) := by
  have h1 : x ^ k ≤ k.factorial * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : x - β * x ^ 2 ≤ 1 / (2 * β) - β / 2 * x ^ 2 := by
    have ht : 1 / (2 * β) * (2 * β) = 1 := by field_simp
    nlinarith [sq_nonneg (β * x - 1)]
  calc x ^ k * Real.exp (-(β * x ^ 2)) ≤ (k.factorial * Real.exp x) * Real.exp (-(β * x ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = k.factorial * Real.exp (x - β * x ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ k.factorial * Real.exp (1 / (2 * β) - β / 2 * x ^ 2) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_gauss {β : ℝ} (hβ : 0 < β) :
    Integrable (fun a : E => Real.exp (-(β * ‖a‖ ^ 2))) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (β : ℂ))
    (by simpa using hβ) 0 (0 : E)).norm
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only [zero_mul, add_zero]
  rw [show -(β : ℂ) * (‖a‖ : ℂ) ^ 2 = ((-(β * ‖a‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]

lemma integrable_wt_smul_powForm {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : SchwartzMap E ℂ)
    (k : ℕ) : Integrable (fun a : E => wt b c h a • powForm k a) := by
  have hβ : 0 < b + c := by positivity
  have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h := apply_nonneg _ _
  refine Integrable.mono' ((integrable_gauss (E := E) (half_pos hβ)).const_mul
    (SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
      k.factorial * Real.exp (1 / (2 * (b + c)))))
    ((continuous_wt b c h).smul (continuous_powForm k)).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  rw [norm_smul]
  have h1 := norm_wt_le b c h a
  have h2 := norm_powForm_le k a
  have h3 := pow_mul_exp_le hβ k (norm_nonneg a)
  calc ‖wt b c h a‖ * ‖powForm k a‖
      ≤ (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2))) *
          (‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ * ‖a‖ ^ k) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
          (‖a‖ ^ k * Real.exp (-((b + c) * ‖a‖ ^ 2))) := by ring
    _ ≤ SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
          (k.factorial * Real.exp (1 / (2 * (b + c))) * Real.exp (-((b + c) / 2 * ‖a‖ ^ 2))) := by
        gcongr
    _ = _ := by ring

lemma coef_apply_const {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : SchwartzMap E ℂ) (k : ℕ) (y : E) :
    coef b c h k (fun _ => y) = ∫ a, wt b c h a * ((inner ℝ a y : ℝ) : ℂ) ^ k := by
  have := ContinuousLinearMap.integral_comp_comm
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun _ => y))
    (integrable_wt_smul_powForm hb hc h k)
  simp only [ContinuousMultilinearMap.apply_apply] at this
  unfold coef
  rw [← this]
  congr 1; funext a
  simp [powForm, innerC, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]

end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

namespace GlobalTheory.ConvSeries

open GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

theorem hasSum_term_integral (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h : SchwartzMap E ℂ) (y : E) :
    HasSum (fun k => term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  set z : E → ℂ := fun a => ((2 * c * inner ℝ a y : ℝ) : ℂ) with hz
  have hzc : Continuous z := by rw [hz]; fun_prop
  let F : ℕ → E → ℂ := fun n a => wt b c h a * (z a ^ n / (n.factorial : ℂ))
  have hF : ∀ n, (∫ a, F n a) =
      (((2 * c) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * coef b c h n (fun _ => y) := by
    intro n
    rw [coef_apply_const hb hc h n y, ← integral_const_mul]
    congr 1; funext a
    simp only [F, z]; push_cast; ring
  have hsum : HasSum (fun n => ∫ a, F n a) (∫ a, wt b c h a * Complex.exp (z a)) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n a => ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) ?_ ?_ ?_ ?_ ?_
    · intro n
      have := continuous_wt b c h
      exact (by simp only [F]; fun_prop : Continuous (F n)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun a => ?_
      simp only [F]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have hza : ‖z a‖ ≤ 2 * c * ‖a‖ * ‖y‖ := by
        have h1 : ‖z a‖ = 2 * c * |inner ℝ a y| := by
          simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two, abs_of_pos hc]
        rw [h1]
        have := abs_real_inner_le_norm a y
        nlinarith
      gcongr
    · exact Eventually.of_forall fun a => (Real.summable_pow_div_factorial _).mul_left _
    · have hts : (fun a => ∑' n : ℕ, ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) =
          fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖) := by
        funext a
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ,
          ← (NormedSpace.expSeries_div_hasSum_exp (2 * c * ‖a‖ * ‖y‖)).tsum_eq]
      rw [hts]
      have hcw := continuous_wt b c h
      refine Integrable.mono' ((integrable_gauss (E := E) hb).const_mul
        (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2)))
        (by fun_prop : Continuous fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)).aestronglyMeasurable
        (Eventually.of_forall fun a => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h := apply_nonneg _ _
      calc ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)
          ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) *
              Real.exp (2 * c * ‖a‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_right (norm_wt_le b c h a) (by positivity)
        _ = SchwartzMap.seminorm ℝ 0 0 h *
              Real.exp (-((b + c) * ‖a‖ ^ 2) + 2 * c * ‖a‖ * ‖y‖) := by
            rw [Real.exp_add]; ring
        _ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2 + -(b * ‖a‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
            nlinarith [sq_nonneg (‖a‖ - ‖y‖)]
        _ = _ := by rw [Real.exp_add]; ring
    · refine Eventually.of_forall fun a => ?_
      rw [Complex.exp_eq_exp_ℂ]
      exact (NormedSpace.expSeries_div_hasSum_exp (z a)).mul_left (wt b c h a)
  have e1 : (fun k => term b c h k y) =
      fun i => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, F i a := by
    funext k
    simp only [term]
    rw [hF]; ring
  have e2 : (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) =
      Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, wt b c h a * Complex.exp (z a) := by
    rw [← integral_const_mul]
    congr 1; funext a
    have key : Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ)) *
        Complex.exp (z a) = Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [z]
      rw [norm_sub_sq_real, real_inner_comm a y]
      push_cast; ring
    unfold wt
    linear_combination (-(Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a)) * key
  rw [e1, e2]
  exact hsum.mul_left _

end GlobalTheory.ConvSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
section
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.EisConstTerm

theorem eisTerm_pair_zero (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ) (z : Emb F → ℂ) (a : F) :
    eisTerm (2 * s) 0 z (a, 0) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ ^ (2 * s) := by
  have hcard : Fintype.card (Emb F) = Module.finrank ℚ F := by
    rw [← NumberField.Embeddings.card F ℂ]
    refine Fintype.card_of_bijective (f := fun τ : Emb F => (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  have hprod : ∏ τ, latPt z (a, 0) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  unfold eisTerm
  rw [hprod, mul_zero, Complex.cpow_zero, mul_one, mul_inv, mul_pow, inv_pow ((2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F), ← pow_mul, mul_comm (Module.finrank ℚ F)]
  congr 1
  rw [← Complex.ofReal_ratCast, inv_pow, inv_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, (even_two_mul s).pow_abs]

theorem spanSingleton_mul_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (ha : a ∈ latM 𝔞) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have h := FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  calc _ ≤ latM 𝔞 * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by gcongr
    _ = (cD⁻¹ * cD) * (((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * 𝔞) := by rw [latM]; ring
    _ = 1 := by rw [inv_mul_cancel₀ hcD, Units.inv_mul, one_mul]

theorem mem_latM_of_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F)
    (ha : FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) : a ∈ latM 𝔞 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ a
      = FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * latM 𝔞 := by
        rw [latM, show ∀ X : FractionalIdeal (𝓞 F)⁰ F, X * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (cD⁻¹ * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) =
          X * (cD * cD⁻¹) * ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) from fun X => by ring,
          mul_inv_cancel₀ hcD, Units.mul_inv, mul_one, mul_one]
    _ ≤ 1 * latM 𝔞 := by gcongr
    _ = latM 𝔞 := one_mul _

theorem absNorm_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (J : Ideal (𝓞 F))
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a *
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J : ℝ) = |((Algebra.norm ℚ a : ℚ) : ℝ)| * (dF F * nrm 𝔞) := by
  have h := congrArg FractionalIdeal.absNorm hJ
  have e1 : FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm J := FractionalIdeal.coeIdeal_absNorm J
  have e2 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) :=
    FractionalIdeal.coeIdeal_absNorm _
  rw [e1, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 F), e2, absNorm_differentIdeal F (𝓞 F)] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs] at h'
  rw [h', dF, nrm, mul_assoc]
  congr 2
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem mk0_eq_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰) (a : F) (ha : a ≠ 0)
    (J : (Ideal (𝓞 F))⁰) (hJ : ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞 := by
  have hu : FractionalIdeal.mk0 F J = toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha) * FractionalIdeal.mk0 F D * 𝔞 := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact hJ
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha)) = 1 :=
    ClassGroup.mk_eq_one_iff.2 ⟨⟨a, by rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  rw [← ClassGroup.mk_mk0 F, hu, map_mul, map_mul, hp, one_mul, ClassGroup.mk_mk0]

theorem exists_spanSingleton_of_mk0_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰)
    (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞) :
    ∃ a : F, a ≠ 0 ∧ ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  set u := FractionalIdeal.mk0 F J * (FractionalIdeal.mk0 F D * 𝔞)⁻¹ with hu_def
  have h1 : ClassGroup.mk F u = 1 := by
    rw [hu_def, map_mul, map_inv, map_mul, ClassGroup.mk_mk0, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hu : (u : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((u : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hx0 : x ≠ 0 := by
    intro h; apply Units.ne_zero u; rw [hu, h, FractionalIdeal.spanSingleton_zero]
  refine ⟨x, hx0, ?_⟩
  have e : FractionalIdeal.mk0 F J = u * (FractionalIdeal.mk0 F D * 𝔞) := by
    rw [hu_def, inv_mul_cancel_right]
  have e' := congrArg Units.val e
  simp only [Units.val_mul, FractionalIdeal.coe_mk0] at e'
  rw [e', hu, mul_assoc]

theorem hasSum_constTerm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 𝔟 s hs D hD Z hZ z hz
  classical
  set C := ClassGroup.mk0 D * ClassGroup.mk F 𝔞 with hC
  let S := {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 = 0}
  let T := {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C}
  let cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  let Jf : F → FractionalIdeal (𝓞 F)⁰ F := fun a => FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hX : cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := mul_ne_zero hcD (Units.ne_zero 𝔞)
  have hne : ∀ c : S, c.1.out.1.1 ≠ 0 := fun c h => c.1.out.2.2.2 (Prod.ext h c.2)
  have hle : ∀ c : S, Jf c.1.out.1.1 ≤ 1 := fun c => spanSingleton_mul_le_one F 𝔞 _ c.1.out.2.1
  let Jof : S → Ideal (𝓞 F) := fun c => Classical.choose (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJof : ∀ c : S, ((Jof c : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Jf c.1.out.1.1 := fun c =>
    Classical.choose_spec (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJnz : ∀ c : S, Jof c ∈ (Ideal (𝓞 F))⁰ := by
    intro c
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have := hJof c
    rw [h0, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot] at this
    simp only [Jf, mul_assoc] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hne c (FractionalIdeal.spanSingleton_eq_zero_iff.1 h)
    · exact hX h
  have hDc : ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = cD := by simp only [cD, hD]
  let f : S → T := fun c => ⟨⟨Jof c, hJnz c⟩, mk0_eq_of_spanSingleton F 𝔞 D _ (hne c) _ (by rw [hDc]; exact hJof c)⟩
  have hsp : ∀ (a : F) (ε : (𝓞 F)ˣ), FractionalIdeal.spanSingleton (𝓞 F)⁰ (((ε : 𝓞 F) : F) * a) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
    intro a ε
    refine (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, ?_⟩).symm
    rw [Units.smul_def, Algebra.smul_def]
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Jof c = Jof c' := congrArg (fun J : T => (J.1 : Ideal (𝓞 F))) h
      have h2 : Jf c.1.out.1.1 = Jf c'.1.out.1.1 := by rw [← hJof, ← hJof, h1]
      have h3 : FractionalIdeal.spanSingleton (𝓞 F)⁰ c.1.out.1.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ c'.1.out.1.1 := by
        simp only [Jf, mul_assoc] at h2
        exact mul_right_cancel₀ hX h2
      obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h3
      apply Subtype.ext
      rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
      apply Quotient.sound
      refine ⟨ε, ?_, ?_⟩
      · rw [← hε, Units.smul_def, Algebra.smul_def]
      · rw [c.2, c'.2, mul_zero]
    · rintro ⟨J, hJ⟩
      obtain ⟨a, ha, hJa⟩ := exists_spanSingleton_of_mk0_eq F 𝔞 D J hJ
      have hJle : Jf a ≤ 1 := by
        have h := FractionalIdeal.coeIdeal_le_one (I := (J : Ideal (𝓞 F))) (S := (𝓞 F)⁰) (P := F)
        rwa [hJa, hDc] at h
      let p : LatPair 𝔞 𝔟 := ⟨(a, 0), mem_latM_of_le_one F 𝔞 a hJle, Submodule.zero_mem _, fun h => ha (congrArg Prod.fst h)⟩
      obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r p (Quotient.mk (latRel 𝔞 𝔟) p).out := Quotient.exact (Quotient.out_eq _).symm
      have h2' : (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = 0 := by rw [h2]; simp [p]
      refine ⟨⟨Quotient.mk _ p, h2'⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show Jof _ = (J : Ideal (𝓞 F))
      refine FractionalIdeal.coeIdeal_injective (K := F) ?_
      show ((Jof _ : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
      rw [hJof, hJa, hDc]
      show Jf (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = Jf a
      rw [h1]
      simp only [Jf, hsp]
      rfl
  let e : S ≃ T := Equiv.ofBijective f hf
  have hZ2 := hZ.2 ((2 * s : ℕ) : ℂ) (by simp; norm_cast; omega)
  rw [← e.hasSum_iff] at hZ2
  have key : (fun c : S => eisClass 𝔞 𝔟 (2 * s) 0 z c.1) = fun c => (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s)) * ((fun J : T => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-((2 * s : ℕ) : ℂ))) ∘ e) c := by
    funext c
    have hN := absNorm_of_spanSingleton F 𝔞 c.1.out.1.1 (Jof c) (hJof c)
    simp only [Function.comp_apply, e, Equiv.ofBijective_apply, f]
    unfold eisClass
    rw [← Prod.mk.eta (p := c.1.out.1), c.2, eisTerm_pair_zero, Complex.cpow_neg, Complex.cpow_natCast]
    have hX0 : ((dF F * nrm 𝔞 : ℝ) : ℂ) ≠ 0 := by
      have h1 : dF F ≠ 0 := by
        unfold dF; rw [abs_ne_zero]; exact_mod_cast NumberField.discr_ne_zero F
      have h2 : nrm 𝔞 ≠ 0 := by
        unfold nrm; rw [Rat.cast_ne_zero, ne_eq, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero 𝔞
      exact_mod_cast mul_ne_zero h1 h2
    rw [← Complex.ofReal_natCast, hN, Complex.ofReal_mul (|_|)]
    have gen : ∀ (K y X : ℂ) (n : ℕ), X ≠ 0 → K * y⁻¹ ^ n = K * X ^ n * ((y * X) ^ n)⁻¹ := by
      intro K y X n hX
      rw [mul_pow, mul_inv, inv_pow, mul_assoc K, mul_comm ((y ^ n)⁻¹), ← mul_assoc (X ^ n), mul_inv_cancel₀ (pow_ne_zero _ hX), one_mul]
    exact gen _ _ _ _ hX0
  rw [key]
  exact hZ2.mul_left _

end GlobalTheory.EisConstTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrInvolution
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.hermitian_congr_involution (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0) :
    ∃ R s : Matrix ι ι ℂ, R.det ≠ 0 ∧ sᴴ = s ∧ s * s = 1 ∧ Rᴴ * s * R = H := by
  have hA : H.IsHermitian := hH
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set d := hA.eigenvalues with hdd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)
  set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs
  set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD
  have key : D * s * D = diagonal (RCLike.ofReal ∘ d) := by
    rw [hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Function.comp_apply]
    split_ifs with h
    · rw [mul_one, hsq, abs_of_pos h]; rfl
    · rw [mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))]
      push_cast; ring_nf; rfl
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsH : sᴴ = s := by
    rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]
  have hss : s * s = 1 := by
    rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hR : (D * star U)ᴴ * s * (D * star U) = H := by
    rw [conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]
    conv_rhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← key]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose]
    rfl
  refine ⟨D * star U, s, ?_, hsH, hss, hR⟩
  intro h0
  apply hd
  rw [← hR, det_mul, det_mul, h0, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBoundStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_similitude_entry_sq_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  first | (exact @GlobalTheory.herm_scale_entry_bound) | (exact GlobalTheory.herm_scale_entry_bound) | (intros; apply GlobalTheory.herm_scale_entry_bound  <;> assumption)
end

