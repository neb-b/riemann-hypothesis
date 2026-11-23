module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
public import GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.EulerFactors
section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex
open scoped NumberField.AdeleRing Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def gammaFactor (s : ℂ) : ℂ := ∏ w, χ.infiniteGamma w s

omit [NumberField K] in
theorem prod_infiniteConst [NumberField K] :
    ∏ w : InfinitePlace K, infiniteConst w = (π : ℂ) ^ nrComplexPlaces K := by
  rw [prod_eq_prod_mul_prod]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w}, infiniteConst w.1 = 1 := fun w ↦ by
    rw [infiniteConst, if_pos w.2]
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w}, infiniteConst w.1 = π := fun w ↦ by
    rw [infiniteConst, if_neg (not_isReal_iff_isComplex.2 w.2)]
  simp only [h1, h2, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

def testFunction : 𝔸[K] → ℂ := schwartzBruhatTensor χ.infiniteSchwartz χ.finiteTestFun

theorem pi_pow_nrComplexPlaces_ne_zero : (π : ℂ) ^ nrComplexPlaces K ≠ 0 :=
  pow_ne_zero _ (ofReal_ne_zero.2 Real.pi_ne_zero)

theorem testFunction_mem : χ.testFunction ∈ schwartzBruhat K :=
  schwartzBruhatTensor_mem _ χ.finiteTestFun_mem

theorem zetaIntegrand_testFunction (s : ℂ) (x : IdeleGroup K) :
    χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s =
      (χ.infiniteSchwartz (homeomorphMixedSpace K (toInfinite K x)) *
          (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) *
          ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
            ℝ) : ℂ) ^ s) *
        (χ.finiteTestFun (toFinite K x) * (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
          ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (χ.toIdele x : ℂ) = (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
      (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule K x : ℝ) : ℂ) ^ s =
      ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
        ℝ) : ℂ) ^ s * ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s := by
    rw [ideleModule_apply, ofReal_mul, mul_cpow_ofReal_nonneg (infiniteModule_pos x).le
      (finiteModule_pos x).le]
    rfl
  rw [hchi, hmod]
  change χ.infiniteSchwartz (homeomorphMixedSpace K (x : 𝔸[K]).1) * χ.finiteTestFun (x : 𝔸[K]).2 *
    _ * _ = _
  have e1 : (x : 𝔸[K]).1 = ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) :=
    rfl
  have e2 : (x : 𝔸[K]).2 = ((toFinite K x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    FiniteAdeleRing (𝓞 K) K) := rfl
  rw [e1, e2]
  ring

theorem globalZeta_testFunction {s : ℂ} (hs : 1 < s.re) :
    globalZeta χ.testFunction χ s = (π : ℂ) ^ nrComplexPlaces K * χ.gammaFactor s * χ.LFunction s := by
  have hs0 : 0 < s.re := by linarith
  set A : (InfiniteAdeleRing K)ˣ → ℂ := fun a ↦ χ.infiniteSchwartz (homeomorphMixedSpace K a) *
    (χ.toIdele (ofInfinite a) : ℂ) * ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s
    with hA
  set B : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun b ↦ χ.finiteTestFun b *
    (χ.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup K, χ.testFunction x * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s = A (toInfinite K x) * B (toFinite K x) :=
    χ.zetaIntegrand_testFunction s
  have hBinv : ∀ b, ∀ w ∈ finiteIntegralUnits K, B (b * w) = B b := fun b w hw ↦ by
    simp only [hB, χ.finiteTestFun_mul_toIdele_mul_cpow, ordFinsupp_ofFinite_mul b hw]
  have hinv : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      χ.testFunction (x * (prodEquiv K).symm (1, w) : IdeleGroup K) *
        (χ.toIdele (x * (prodEquiv K).symm (1, w)) : ℂ) *
        ((ideleModule K (x * (prodEquiv K).symm (1, w)) : ℝ) : ℂ) ^ s =
      χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    intro x w hw
    rw [hF, hF, map_mul, map_mul]
    have h1 : toInfinite K ((prodEquiv K).symm (1, w)) = 1 := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).1 = 1
      rw [ContinuousMulEquiv.apply_symm_apply]
    have h2 : toFinite K ((prodEquiv K).symm (1, w)) = w := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).2 = w
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [h1, h2, mul_one, hBinv _ w hw]
  have h := hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits
    (integrable_globalZetaIntegrand χ.testFunction_mem χ hs) hinv
  have hc : ∀ c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K,
      ∫ a, χ.testFunction ((prodEquiv K).symm (a, c.out) : IdeleGroup K) *
        (χ.toIdele ((prodEquiv K).symm (a, c.out)) : ℂ) *
        ((ideleModule K ((prodEquiv K).symm (a, c.out)) : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      (∏ w, infiniteConst w * χ.infiniteGamma w s) * B c.out := by
    intro c
    have hsymm : ∀ a, toInfinite K ((prodEquiv K).symm (a, c.out)) = a ∧
        toFinite K ((prodEquiv K).symm (a, c.out)) = c.out := fun a ↦ by
      constructor
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).1 = a
        rw [ContinuousMulEquiv.apply_symm_apply]
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).2 = c.out
        rw [ContinuousMulEquiv.apply_symm_apply]
    simp only [hF, (hsymm _).1, (hsymm _).2]
    rw [integral_mul_const, ← χ.integral_infiniteSchwartz hs0]
  simp only [hc] at h
  have h2 := (χ.hasSum_finiteTestFun hs).mul_left (∏ w, infiniteConst w * χ.infiniteGamma w s)
  rw [globalZeta, h.unique h2, Finset.prod_mul_distrib, prod_infiniteConst, gammaFactor]

end HeckeCharacter

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierInfinite
section
open NumberField InfinitePlace MeasureTheory Complex ComplexConjugate NumberField.mixedEmbedding
open scoped Real FourierTransform Classical

namespace GroundTheory.Global

noncomputable section

theorem fourier_pow_mul_realGaussian {n : ℕ} (hn : n < 2) (y : ℝ) :
    𝓕 (fun t : ℝ ↦ (t : ℂ) ^ n * realGaussian t) y = (-I) ^ n * ((y : ℂ) ^ n * realGaussian y) := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · simp only [pow_zero, one_mul]
    rw [show (fun t : ℝ ↦ realGaussian t) = realGaussian from rfl, fourier_realGaussian]
  · simp only [pow_one]
    rw [show (fun t : ℝ ↦ (t : ℂ) * realGaussian t) = realGaussianOdd from rfl,
      fourier_realGaussianOdd]
    rfl

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem infiniteSchwartz_eq_prod (x : mixedSpace K) :
    χ.infiniteSchwartz x =
      (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs *
        realGaussian (x.1 w)) *
      ∏ w : {w // IsComplex w}, complexGaussian (-χ.infiniteWeight w) (x.2 w) := by
  rw [infiniteSchwartz_apply, infinitePoly]
  simp only [complexGaussian, Int.natAbs_neg, realGaussian_eq_ofReal, Finset.prod_mul_distrib]
  have hc : ∀ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs =
      (if 0 ≤ -χ.infiniteWeight w then x.2 w ^ (χ.infiniteWeight w).natAbs
        else conj (x.2 w) ^ (χ.infiniteWeight w).natAbs) := fun w ↦ by
    by_cases h : 0 < χ.infiniteWeight w
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  simp only [hc]
  have hexp : ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * x.1 w ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2) := by
    have e2 : ∀ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2) =
        ((Real.exp (-(2 * π * ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := fun w ↦ by
      rw [ofReal_exp]; push_cast; ring_nf
    simp only [e2]
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum,
      ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by ring
  rw [hexp]
  ring

theorem fourierChar_neg_mixedTraceForm (x y : mixedSpace K) :
    ((𝐞 (-mixedTraceForm K x y) : Circle) : ℂ) =
      (∏ w : {w // IsReal w}, ((𝐞 (-(x.1 w * y.1 w)) : Circle) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((𝐞 (-(2 * (x.2 w * y.2 w).re)) : Circle) : ℂ) := by
  rw [mixedTraceForm_apply', neg_add, AddChar.map_add_eq_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, addChar_map_finsetSum, addChar_map_finsetSum, Circle.coe_mul]
  congr 1 <;> exact map_prod Circle.coeHom _ _

theorem mixedFourier_infiniteSchwartz (y : mixedSpace K) :
    mixedFourier K χ.infiniteSchwartz y =
      (∏ w, (-I) ^ (χ.infiniteWeight w).natAbs) * (χ⁻¹).infiniteSchwartz y := by
  set A : ∀ w : {w // IsReal w}, ℝ → ℂ := fun w t ↦ ((𝐞 (-(t * y.1 w)) : Circle) : ℂ) *
    ((t : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian t)
  set B : ∀ w : {w // IsComplex w}, ℂ → ℂ := fun w z ↦
    ((𝐞 (-(2 * (z * y.2 w).re)) : Circle) : ℂ) * complexGaussian (-χ.infiniteWeight w) z
  have hint : ∀ x : mixedSpace K, 𝐞 (-mixedTraceForm K x y) • χ.infiniteSchwartz x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, fourierChar_neg_mixedTraceForm, infiniteSchwartz_eq_prod]
    simp only [A, B, Finset.prod_mul_distrib]
    ring
  have hA : ∀ w : {w // IsReal w}, ∫ t, A w t =
      (-I) ^ (χ.infiniteWeight w).natAbs *
        ((y.1 w : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian (y.1 w)) := by
    intro w
    have hm := χ.infiniteWeight_of_isReal w.2
    rw [← fourier_pow_mul_realGaussian (by omega), Real.fourier_real_eq]
    rfl
  have hB : ∀ w : {w // IsComplex w}, ∫ z, B w z =
      (-I) ^ (χ.infiniteWeight w).natAbs * complexGaussian (χ.infiniteWeight w) (y.2 w) / 2 := by
    intro w
    have h := congrFun (complexFourier_complexGaussian (-χ.infiniteWeight w)) (y.2 w)
    rw [neg_neg, Int.natAbs_neg, complexFourier, complexPlaceMeasure, integral_smul_measure] at h
    simp only [ENNReal.toReal_ofNat, Circle.smul_def, smul_eq_mul] at h
    rw [← h]
    simp only [B, Complex.real_smul]
    push_cast
    ring
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun a : {w // IsReal w} → ℝ ↦ ∏ w, A w (a w))
    (g := fun b : {w // IsComplex w} → ℂ ↦ ∏ w, B w (b w)), integral_fintype_prod_volume_eq_prod,
    integral_fintype_prod_volume_eq_prod]
  simp only [hA, hB]
  rw [(χ⁻¹).infiniteSchwartz_eq_prod, prod_eq_prod_mul_prod]
  have hr : ∀ w : {w // IsReal w}, (χ⁻¹).infiniteWeight w = χ.infiniteWeight w := fun w ↦
    χ.infiniteWeight_inv_of_isReal w.2
  have hc : ∀ w : {w // IsComplex w}, (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w := fun w ↦
    χ.infiniteWeight_inv_of_isComplex w.2
  simp only [hr, hc, neg_neg, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Complex.real_smul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have h2 : (2 : ℂ) ^ Fintype.card {w : InfinitePlace K // IsComplex w} ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp

end HeckeCharacter

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.GlobalZetaSplit
section
open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def partialZetaSum (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  ∑' ξ : Kˣ, f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
    (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ)

theorem partialZetaSum_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) {δ : normOneSubgroup K}
    (hδ : δ ∈ diagonalNormOne K) : partialZetaSum w f χ t (u * δ) = partialZetaSum w f χ t u := by
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hδ
  obtain ⟨ξ₀, hξ₀⟩ := hδ
  unfold partialZetaSum
  conv_rhs => rw [← (Equiv.mulRight ξ₀).tsum_eq]
  refine tsum_congr fun ξ ↦ ?_
  have hχ : χ.toIdele (moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [Subgroup.coe_mul, ← hξ₀, ← mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]
  have hf : diagonal K ξ * moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K) =
      diagonal K ((Equiv.mulRight ξ₀) ξ) * moduleSection w t * (u : IdeleGroup K) := by
    rw [Subgroup.coe_mul, ← hξ₀, Equiv.coe_mulRight, map_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [hχ, hf]

def partialZetaClass (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : normOneSubgroup K ⧸ diagonalNormOne K → ℂ :=
  Quotient.lift (s := QuotientGroup.leftRel (diagonalNormOne K)) (partialZetaSum w f χ t)
    fun u v h ↦ by
      have h' : u⁻¹ * v ∈ diagonalNormOne K := QuotientGroup.leftRel_apply.1 h
      conv_rhs => rw [← mul_inv_cancel_left u v]
      rw [partialZetaSum_mul w f χ t u h']

def partialZeta (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ c, partialZetaClass w f χ t c ∂normOneClassMeasure K

theorem measurable_partialZetaSum (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) : Measurable (partialZetaSum w f χ t) := by
  refine Measurable.tsum fun ξ ↦ Continuous.measurable ?_
  have hu : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have hu' : Continuous fun u : normOneSubgroup K ↦
      diagonal K ξ * moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  exact (hf.comp (Units.continuous_val.comp hu')).mul
    (continuous_subtype_val.comp (χ.continuous_toIdele.comp hu))

theorem partialZeta_eq_setIntegral (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    partialZeta w f χ t =
      ∫ u in normOneFundamentalDomain K, partialZetaSum w f χ t u ∂normOneMeasure K := by
  have hm : Measurable (partialZetaClass w f χ t) :=
    QuotientGroup.measurable_from_quotient.2 (measurable_partialZetaSum w hf χ t)
  rw [partialZeta, normOneClassMeasure,
    integral_map QuotientGroup.measurable_coe.aemeasurable hm.aestronglyMeasurable]
  rfl

theorem zetaIntegrand_diagonal_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (s : ℂ) (ξ : Kˣ) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) :
    f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℂ) *
        ((ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℝ) : ℂ) ^ s =
      f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ) * ((t : ℝ) : ℂ) ^ s := by
  have hu : ideleModule K (u : IdeleGroup K) = 1 := u.2
  have hmod : ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) = t := by
    rw [map_mul, map_mul, ideleModule_diagonal, one_mul, ideleModule_moduleSection, hu, mul_one]
  have hχ : χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, one_mul]
  simp only [hmod, hχ]

theorem globalZeta_eq_integral_partialZeta (w : InfinitePlace K) {f : 𝔸[K] → ℂ}
    (hf : f ∈ schwartzBruhat K) (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s) posRealMeasure ∧
      globalZeta f χ s = ∫ t, partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s ∂posRealMeasure := by
  have hfc := continuous_of_mem_schwartzBruhat hf
  set G : IdeleGroup K → ℂ := fun x ↦ f x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s
    with hGdef
  have hG : Integrable G (ideleMeasure K) := integrable_globalZetaIntegrand hf χ hs
  have hg : Integrable (fun p : normOneSubgroup K × {r : ℝ // 0 < r} ↦
      G ((p.1 : IdeleGroup K) * moduleSection w p.2))
      ((normOneMeasure K).prod posRealMeasure) := by
    rw [← map_normOneSplitting_eq_prod w]
    refine (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv _).2 ?_
    convert hG using 1
    funext x
    exact congrArg G ((normOneSplitting w).symm_apply_apply x)
  have hae : (fun t ↦ ∫ u, G ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K)
      =ᵐ[posRealMeasure] fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s := by
    filter_upwards [hg.prod_left_ae] with t ht
    rw [integral_normOneMeasure_eq_setIntegral_tsum ht, partialZeta_eq_setIntegral w hfc,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp only [partialZetaSum]
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ ↦ ?_
    have hx : ((diagonalToNormOne K ξ * u : normOneSubgroup K) : IdeleGroup K) *
        moduleSection w t = diagonal K ξ * moduleSection w t * (u : IdeleGroup K) := by
      rw [Subgroup.coe_mul, coe_diagonalToNormOne, mul_right_comm]
    rw [hx]
    exact zetaIntegrand_diagonal_mul w f χ s ξ t u
  refine ⟨hg.integral_prod_right.congr hae, ?_⟩
  rw [globalZeta, integral_ideleMeasure_eq_integral_normOne w hG]
  exact integral_congr_ae hae

end

end GroundTheory.Global
end

