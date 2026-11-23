module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
section
open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

theorem card_mul_rpow_prod_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp

section General

variable {K : Type*} [Field K] [NumberField K]

theorem norm_eq_prod_complexEmbeddings (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  simp

theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp

theorem abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [← norm_prod, ← norm_eq_prod_complexEmbeddings, Complex.norm_ratCast]

theorem finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _

theorem finrank_mul_abs_norm_rpow_le_sum_sq (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]

theorem one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem absNorm_le_abs_norm_of_mem {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (by simpa using hI')
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1

theorem finrank_mul_absNorm_rpow_le_sum_sq {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : ((FractionalIdeal.absNorm J : ℚ) : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast absNorm_le_abs_norm_of_mem hx h0
  have h2 : (0 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  gcongr


variable (K) in
theorem dual_one_eq_inv_differentIdeal :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]


variable (K) in
theorem absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp

theorem finrank_mul_discr_rpow_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_absNorm_rpow_le_sum_sq hx h0
  rw [absNorm_inv_differentIdeal] at h
  rw [neg_div, Real.rpow_neg (abs_nonneg _), ← Real.inv_rpow (abs_nonneg _)]
  simpa using h

theorem finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_discr_rpow_le_sum_sq hx h0
  rw [neg_div, Real.rpow_neg (abs_nonneg _), div_eq_inv_mul, Real.rpow_mul (abs_nonneg _),
    Real.rpow_two] at h
  rw [rootDiscr_def, div_eq_mul_inv]
  simpa using h

theorem finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine finrank_mul_discr_rpow_le_sum_sq ?_ h0
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  exact hx

end General

section TotallyReal

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]


omit [NumberField F] in
variable (F) in
theorem bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩


variable (F) in
theorem card_realEmbeddings : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)

theorem trace_eq_sum_realEmbeddings (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm

end TotallyReal

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
section
open MeasureTheory Set Real
open scoped Nat ComplexConjugate

namespace GlobalTheory

section General

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def complexGaussian (g : ℕ) : Measure E :=
  volume.withDensity fun z => ENNReal.ofReal ((π ^ g)⁻¹ * exp (-‖z‖ ^ 2))

variable {E}

theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => exp (-b * ‖z‖ ^ 2) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef h] at h1
  exact absurd h1 (by positivity)

theorem integral_exp_neg_mul_norm_sq {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) {b : ℝ}
    (hb : 0 < b) : ∫ z : E, exp (-b * ‖z‖ ^ 2) = (π / b) ^ g := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hE, ← rpow_natCast]
  congr 1
  push_cast
  ring

theorem isProbabilityMeasure_complexGaussian {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) :
    IsProbabilityMeasure (complexGaussian E g) := by
  constructor
  have h := integral_exp_neg_mul_norm_sq hE one_pos
  have hi := integrable_exp_neg_mul_norm_sq (E := E) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (.of_forall fun z => by positivity),
    integral_const_mul, h, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar volume (f := fun r => r ^ n * exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ E - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

end General

section Combinatorics

end Combinatorics

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Kernel

section Monomials

theorem finrank_real_euclideanSpace_complex (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

theorem volume_preserving_ofLp_complex (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
  change MeasurePreserving e
  refine ⟨e.continuous.measurable, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e volume = c • (volume : Measure (ι → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have h1 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) = π ^ Fintype.card ι := by
    rw [integral_fintype_prod_volume_eq_pow fun w : ℂ => exp (-1 * ‖w‖ ^ 2),
      integral_exp_neg_mul_norm_sq (E := ℂ) (g := 1) (by simp) one_pos]
    simp
  have h2 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) ∂(Measure.map e volume) =
      π ^ Fintype.card ι := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have := integral_exp_neg_mul_norm_sq (finrank_real_euclideanSpace_complex ι) one_pos
    rw [div_one] at this
    rw [← this]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [← exp_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    rfl
  rw [hc, integral_smul_nnreal_measure, h1, NNReal.smul_def, smul_eq_mul,
    mul_eq_right₀ (by positivity)] at h2
  rw [hc, show c = 1 by exact_mod_cast h2, one_smul]

end Monomials

section Fin

end Fin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.L2OpNormConjTransposeExpMulSignMulExpSubLe
section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace GlobalTheory

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]


theorem norm_dotProduct_mulVec_star_le (A : Matrix n n ℂ) (x : n → ℂ) :
    ‖x ⬝ᵥ A *ᵥ star x‖ ≤ ‖A‖ * ∑ k, ‖x k‖ ^ 2 := by
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 (star x) with hy
  have h := l2_opNorm_mulVec A y
  have h1 := norm_inner_le_norm (𝕜 := ℂ) y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y))
  have h2 : ‖y‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by simp [hy, EuclideanSpace.norm_sq_eq]
  have h3 : inner ℂ y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y)) = x ⬝ᵥ A *ᵥ star x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [hy]
  rw [← h3, ← h2]
  refine h1.trans ?_
  nlinarith [norm_nonneg y]

end OpNorm

section LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

end LogDet

section Inertia

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    x ⬝ᵥ diagonal d *ᵥ star x = ∑ k, d k * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

theorem le_re_dotProduct_diagonal_add_of_support {j : n → ℂ} (E : Matrix n n ℂ) {x : n → ℂ}
    (hx : ∀ k, x k ≠ 0 → j k = 1) :
    (1 - ‖E‖) * ∑ k, ‖x k‖ ^ 2 ≤ (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re := by
  have h1 : (x ⬝ᵥ diagonal j *ᵥ star x).re = ∑ k, ‖x k‖ ^ 2 := by
    rw [dotProduct_diagonal_mulVec_star, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : x k = 0
    · simp [h]
    · rw [hx k h, one_mul, Complex.ofReal_re]
  have h2 := norm_dotProduct_mulVec_star_le E x
  have h3 := abs_le.1 (Complex.abs_re_le_norm (x ⬝ᵥ E *ᵥ star x))
  rw [add_mulVec, dotProduct_add, Complex.add_re, h1]
  linarith [h3.1]

theorem sum_norm_sq_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < ∑ k, ‖x k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ k, by have : x k ≠ 0 := hk; positivity⟩

theorem re_dotProduct_diagonal_add_pos_of_support {j : n → ℂ} {E : Matrix n n ℂ} (hE : ‖E‖ < 1)
    {x : n → ℂ} (hx0 : x ≠ 0) (hx : ∀ k, x k ≠ 0 → j k = 1) :
    0 < (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re :=
  (mul_pos (by linarith) (sum_norm_sq_pos hx0)).trans_le
    (le_re_dotProduct_diagonal_add_of_support E hx)

theorem posDef_one_add {E : Matrix n n ℂ} (hE : E.IsHermitian) (hE1 : ‖E‖ < 1) :
    (1 + E).PosDef := by
  have hH : (1 + E).IsHermitian := isHermitian_one.add hE
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h := re_dotProduct_diagonal_add_pos_of_support (j := fun _ => 1) hE1
    (star_ne_zero.2 hx) fun _ _ => rfl
  rw [star_star, diagonal_one] at h
  rw [Complex.pos_iff]
  exact ⟨h, (hH.im_star_dotProduct_mulVec_self x).symm⟩

end Inertia

section Exp

open NormedSpace

theorem norm_exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (x : A) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    ← sub_sub] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Exp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
section
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix

namespace GlobalTheory

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_gram_eq_normSq_det {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by
  have h : b.toBasis.det v = (Matrix.of fun i j ↦ b.repr (v j) i).det := by
    rw [Basis.det_apply]; congr 1
  rw [gram_eq_conjTranspose_mul b v, det_mul, det_conjTranspose, h, RCLike.star_def,
    RCLike.conj_mul]
  push_cast; rfl

theorem det_gram_le_of_finrank_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (h : finrank 𝕜 V = Fintype.card ι) (v : ι → V) :
    (gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  let e := (Fintype.equivFin ι).symm
  have h' : finrank 𝕜 V = Fintype.card (Fin (Fintype.card ι)) := by simpa using h
  have h1 : (gram 𝕜 v).det = (gram 𝕜 (v ∘ e)).det := by
    rw [← det_submatrix_equiv_self e]; rfl
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h' (v ∘ e)
  have hb : b.toBasis.det (v ∘ e) = ∏ i, ⟪b i, (v ∘ e) i⟫_𝕜 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det h' _
  rw [h1, det_gram_eq_normSq_det b, hb, RCLike.ofReal_le_ofReal, norm_prod, ← Finset.prod_pow,
    ← e.prod_comp (fun i ↦ ‖v i‖ ^ 2)]
  refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  gcongr
  simpa using norm_inner_le_norm (𝕜 := 𝕜) (b i) (v (e i))

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  let v : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 fun i ↦ A i j
  have h := det_gram_le_of_finrank_eq (𝕜 := 𝕜) (by simp) v
  rw [det_gram_eq_normSq_det (EuclideanSpace.basisFun ι 𝕜), RCLike.ofReal_le_ofReal] at h
  have h2 : (EuclideanSpace.basisFun ι 𝕜).toBasis.det v = A.det := by
    rw [Basis.det_apply]; congr 1
  rw [h2] at h
  refine h.trans_eq (Finset.prod_congr rfl fun j _ ↦ ?_)
  rw [EuclideanSpace.norm_sq_eq]

theorem posSemidef_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.nonneg
  have h := norm_det_sq_le_prod_col B
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜)] at h
  convert h using 1
  · rw [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    push_cast; rfl
  · push_cast
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [Matrix.mul_apply, RCLike.conj_mul]

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]

end Gram

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem linearIndependent_real_of_int_of_discrete {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by
  have hle : span ℤ (Set.range v) ≤ L := span_le.2 (Set.range_subset_iff.2 hv)
  have hd : DiscreteTopology (span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion hle)
      (continuous_inclusion hle) (Set.inclusion_injective hle)
  rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
  rw [Real.finrank_eq_int_finrank_of_discrete hd, hli]

variable [MeasurableSpace E] [BorelSpace E]

theorem covolume_span_basis_eq_sqrt_det_gram [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    det_gram_eq_normSq_det o, measureReal_def, o.coe_toBasis, o.volume_parallelepiped]
  simp [Real.sqrt_sq_eq_abs]

theorem covolume_eq_sqrt_det_gram [DecidableEq ι] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = √(gram ℝ fun i ↦ (b i : E)).det := by
  have h := covolume_span_basis_eq_sqrt_det_gram (b.ofZLatticeBasis ℝ L)
  rw [b.ofZLatticeBasis_span ℝ] at h
  rw [h]
  congr 3
  ext i
  simp

end Covolume

end GlobalTheory
end

