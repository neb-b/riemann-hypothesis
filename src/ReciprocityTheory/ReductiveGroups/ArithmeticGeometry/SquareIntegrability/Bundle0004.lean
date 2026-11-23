module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RSubMean

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegralMulConjGaussianEqCoeffNormSq
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable def fa1M {g : ℕ} (α : Fin g →₀ ℕ) : ℝ :=
  (Real.pi ^ g)⁻¹ * ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)

theorem monomialMass_pos {g : ℕ} (α : Fin g →₀ ℕ) : 0 < fa1M α :=
  mul_pos (by positivity) (integral_norm_monomial_sq_gaussian_pos α)

theorem integral_norm_monomial_sq_gaussian_eq {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.pi ^ g * fa1M α := by
  unfold fa1M
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ Real.pi_ne_zero), one_mul]

noncomputable def fa1K {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) : ℝ :=
  ∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α

noncomputable def fa1N {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖AddMonoidAlgebra.coeff p α‖ ^ 2 * fa1M α

theorem monomialKernel_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    0 ≤ fa1K p z := by
  unfold fa1K
  exact Finset.sum_nonneg fun α _ => div_nonneg (by positivity) (monomialMass_pos α).le

theorem coeffNormSq_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : 0 ≤ fa1N p := by
  unfold fa1N
  exact Finset.sum_nonneg fun α _ => mul_nonneg (by positivity) (monomialMass_pos α).le

theorem eval_eq_sum_coeff_mul_monomial {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    MvPolynomial.eval (fun i => z i) p = ∑ α ∈ p.support, AddMonoidAlgebra.coeff p α * monomialOfMultiindex α z := by
  first
  | (simp [MvPolynomial.eval_eq', monomialOfMultiindex]; done)
  | (simp [MvPolynomial.eval_eq, monomialOfMultiindex, Finsupp.prod]; done)
  | (rw [MvPolynomial.eval_eq']; unfold monomialOfMultiindex; done)

theorem norm_eval_sq_le {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖MvPolynomial.eval (fun i => z i) p‖ ^ 2 ≤ fa1N p * fa1K p z := by
  rw [eval_eq_sum_coeff_mul_monomial]
  have hM : ∀ α : Fin g →₀ ℕ, 0 < fa1M α := monomialMass_pos
  have h1 : ‖∑ α ∈ p.support, AddMonoidAlgebra.coeff p α * monomialOfMultiindex α z‖ ≤
      ∑ α ∈ p.support, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun α _ => ?_))
    have hs : Real.sqrt (fa1M α) ≠ 0 := (Real.sqrt_pos.mpr (hM α)).ne'
    rw [norm_mul]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq p.support
    (fun α => ‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) (fun α => ‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))
  have h3 : ∀ α, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) ^ 2 = ‖AddMonoidAlgebra.coeff p α‖ ^ 2 * fa1M α :=
    fun α => by rw [mul_pow, Real.sq_sqrt (hM α).le]
  have h4 : ∀ α, (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) ^ 2 = ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α :=
    fun α => by rw [div_pow, Real.sq_sqrt (hM α).le]
  simp only [h3, h4] at h2
  unfold fa1N fa1K
  calc _ ≤ (∑ α ∈ p.support, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem integrable_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-b * ‖z‖ ^ 2)) := by
  simp only [fa1K, Finset.sum_mul]
  refine integrable_finsetSum _ (fun α _ => ?_)
  have := (integrable_norm_monomial_sq_gaussian α hb).const_mul (fa1M α)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only; ring

theorem integral_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) = Real.pi ^ g * p.support.card := by
  have hint : ∀ α : Fin g →₀ ℕ,
      MeasureTheory.Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    intro α
    by_contra h
    apply (monomialMass_pos α).ne'
    unfold fa1M
    rw [MeasureTheory.integral_undef h, mul_zero]
  unfold fa1K
  have hfun : (fun z : EuclideanSpace ℂ (Fin g) =>
      (∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α) * Real.exp (-‖z‖ ^ 2)) =
      fun z => ∑ α ∈ p.support, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hfun, MeasureTheory.integral_finsetSum _ (fun α _ => (hint α).const_mul _)]
  have h2 : ∀ α ∈ p.support,
      ∫ z, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) = Real.pi ^ g := by
    intro α _
    rw [MeasureTheory.integral_const_mul, integral_norm_monomial_sq_gaussian_eq, mul_comm (Real.pi ^ g), ← mul_assoc,
      inv_mul_cancel₀ (monomialMass_pos α).ne', one_mul]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring

theorem integral_monomialKernel_mul_gaussian_half {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) := by
  simp only [fa1K, Finset.sum_mul]
  rw [integral_finsetSum _ (fun α _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    have : ∀ z : EuclideanSpace ℂ (Fin g),
        ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
        (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := fun z => by ring
    simp only [this]
    rw [integral_const_mul, integral_norm_monomial_sq_gaussian_half, integral_norm_monomial_sq_gaussian_eq]
    have := (monomialMass_pos α).ne'
    field_simp
  · have := (integrable_norm_monomial_sq_gaussian α (b := 1 / 2) (by norm_num)).const_mul (fa1M α)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring

theorem integral_mul_conj_gaussian_eq_coeffNormSq {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) :
    (((Real.pi ^ g)⁻¹ : ℝ) : ℂ) * ∫ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ((fa1N p : ℝ) : ℂ) := by
  have hexp : ∀ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ∑ α ∈ p.support, ∑ β ∈ p.support,
        (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
          (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hF, eval_eq_sum_coeff_mul_monomial, map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [map_mul]; ring
  simp only [hexp]
  have hint : ∀ α β : Fin g →₀ ℕ, Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
    fun α β => (integrable_monomial_mul_conj_gaussian α β).const_mul _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hint α β))]
  have hin : ∀ α ∈ p.support, ∫ z : EuclideanSpace ℂ (Fin g), ∑ β ∈ p.support,
      (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (((‖AddMonoidAlgebra.coeff p α‖ ^ 2 * (Real.pi ^ g * fa1M α)) : ℝ) : ℂ) := by
    intro α hα
    rw [integral_finsetSum _ (fun β _ => hint α β)]
    rw [Finset.sum_eq_single_of_mem α hα (fun β _ hβ => by
      rw [integral_const_mul, integral_monomial_mul_conj_gaussian_eq_zero (Ne.symm hβ), mul_zero])]
    rw [integral_const_mul]
    have h1 : ∀ z : EuclideanSpace ℂ (Fin g),
        monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex α z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
          ((‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp only [h1]
    rw [integral_complex_ofReal, integral_norm_monomial_sq_gaussian_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [Finset.sum_congr rfl hin, fa1N]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have : (Real.pi : ℂ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  field_simp

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaSA
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex
open scoped Matrix

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_Hf_im (x y : EuclideanSpace ℂ ι) :
    (Hf x y).im = inner ℝ y ((-I : ℂ) • x) := by
  simp only [Hf, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | rw [Complex.inner]
    | rw [real_inner_eq_re_inner ℂ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, RCLike.re_to_complex,
    RCLike.inner_apply]
  ring

def lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι :=
  ((-I : ℂ) • (LinearMap.id : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)).restrictScalars ℝ

lemma lemSJ_apply (x : EuclideanSpace ℂ ι) : (lemSJ : _ →ₗ[ℝ] _) x = (-I : ℂ) • x := rfl

lemma lemSJ_det : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| = 1 := by
  have h2 : ∀ x : EuclideanSpace ℂ ι, (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (lemSJ x) = -x := by
    intro x
    rw [lemSJ_apply, lemSJ_apply, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  have hJJ : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) * lemSJ = -1 :=
    LinearMap.ext fun x => h2 x
  have h4 : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    have e : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = (lemSJ * lemSJ) * (lemSJ * lemSJ) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hJJ, neg_one_mul, neg_neg]
  have hd : LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    rw [← map_pow, h4, map_one]
  have ha : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| ^ 4 = 1 := by
    rw [← abs_pow, hd, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).1 ha

lemma lemS_Hf_sum {n : ℕ} (c : Fin n → ℤ) (v : Fin n → EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) :
    (Hf (∑ i, c i • v i) y).im = ∑ i, (c i : ℝ) * (Hf (v i) y).im := by
  rw [lemS_Hf_im]
  simp only [lemS_Hf_im, Finset.smul_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]

def lemSG {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => (Hf (b i) (b k)).im

lemma lemSG_det {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (b₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    (lemSG b).det = LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) *
      b₀.toBasis.det b * b₀.toBasis.det b := by
  have hG : lemSG b = (b₀.toBasis.toMatrix b)ᵀ *
      (LinearMap.toMatrix b₀.toBasis b₀.toBasis (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _))ᵀ *
      b₀.toBasis.toMatrix b := by
    ext i k
    have e1 : lemSG b i k = inner ℝ (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) := by
      simp only [lemSG, Matrix.of_apply, lemS_Hf_im, lemSJ_apply]
    have e2 : ∀ j, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) =
        ∑ l, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b₀ l)) * inner ℝ (b₀ l) (b i) := by
      intro j
      conv_lhs => rw [← b₀.sum_repr' (b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, real_inner_smul_right, mul_comm]
    rw [e1, ← b₀.sum_inner_mul_inner (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i))]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.coe_toBasis, e2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, real_inner_comm (b₀ j) (b k)]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    LinearMap.det_toMatrix, Module.Basis.det_apply]
  ring


set_option maxHeartbeats 800000 in
lemma lemSG_inv (Y : GT ι) :
    ∃ C : Matrix (Fin (2 * Fintype.card ι)) (Fin (2 * Fintype.card ι)) ℤ,
      (C.map (Int.cast : ℤ → ℝ)) * lemSG Y.b = 1 := by
  classical
  have hx : ∀ k, ∃ x ∈ lat Y.b, ∀ y : lat Y.b,
      ((((Y.b.restrictScalars ℤ).coord k).toAddMonoidHom y : ℤ) : ℝ) =
        (Hf x (y : EuclideanSpace ℂ ι)).im :=
    fun k => Y.perfect _
  choose x hxl hxφ using hx
  refine ⟨Matrix.of fun k i => (Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i, ?_⟩
  ext k m
  have hsum : x k = ∑ i, ((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i) • Y.b i := by
    have h := congrArg (fun v : lat Y.b => (v : EuclideanSpace ℂ ι))
      ((Y.b.restrictScalars ℤ).sum_repr ⟨x k, hxl k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  have h2 : (Hf (x k) (Y.b m)).im =
      ∑ i, (((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i : ℤ) : ℝ) * (Hf (Y.b i) (Y.b m)).im := by
    conv_lhs => rw [hsum]
    exact lemS_Hf_sum _ _ _
  have h3 : (Hf (x k) (Y.b m)).im =
      ((((Y.b.restrictScalars ℤ).coord k) ((Y.b.restrictScalars ℤ) m) : ℤ) : ℝ) := by
    have h := hxφ k ((Y.b.restrictScalars ℤ) m)
    rw [LinearMap.toAddMonoidHom_coe, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, lemSG, Matrix.one_apply]
  rw [← h2, h3, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases eq_or_ne k m with rfl | hkm
  · simp
  · simp [hkm, Ne.symm hkm]

lemma lemS_detM_le (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| ≤ 1 := by
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have hdet := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one, lemSG_det Y.b b₀, ← Int.cast_det] at hdet
  have hJ := lemSJ_det (ι := ι)
  have hC0 : C.det ≠ 0 := by
    rintro h
    rw [h] at hdet
    simp at hdet
  have h1 : (1 : ℝ) ≤ |(C.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hC0
  have habs := congrArg abs hdet
  simp only [abs_mul, abs_one, hJ, one_mul] at habs
  nlinarith [abs_nonneg (b₀.toBasis.det Y.b), mul_nonneg (sub_nonneg.2 h1)
    (mul_self_nonneg |b₀.toBasis.det Y.b|)]

lemma lemS_vol_le (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) ≤ 1 := by
  classical
  have hr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [Module.finrank_eq_card_basis Y.b, Fintype.card_fin]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis]
  have h1 : volume (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
      OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  rw [h1, mul_one]
  calc ENNReal.ofReal |b₀.toBasis.det Y.b| ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal (lemS_detM_le Y b₀)
    _ = 1 := ENNReal.ofReal_one

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaSB
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex Metric

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  first
  | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
  | rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace]
  | (rw [(WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq, Module.finrank_pi_fintype]
     simp [Complex.finrank_real_complex, mul_comm])
  | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]

theorem lemS_local (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F)
    (v0 : EuclideanSpace ℂ ι) :
    ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) ≤
      2 * (q : ℝ) ^ Fintype.card ι *
        ∫ u in closedBall v0 (Real.sqrt (2 * Fintype.card ι) / Real.sqrt (q * Real.pi)),
          ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
  set s := Real.sqrt (q * Real.pi) with hs
  set ρ := Real.sqrt (2 * Fintype.card ι) with hρ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q * Real.pi := mul_pos (by linarith) Real.pi_pos
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt hqpos.le
  let eC : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  let eR : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (Fintype.equivFin ι)
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin (Fintype.card ι)) → EuclideanSpace ℂ ι,
      w = fun z => s⁻¹ • eC.symm z := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℂ (Fin (Fintype.card ι)) → ℂ,
      G = fun z => F (v0 + w z) * Complex.exp (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)) :=
    ⟨_, rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ Hf : EuclideanSpace ℂ ι → ℝ,
      Hf = fun u => ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := ⟨_, rfl⟩
  have hwd : Differentiable ℂ w := by
    rw [hw]
    exact (eC.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiable).const_smul s⁻¹
  have hGd : Differentiable ℂ G := by
    rw [hG]
    refine (hF.comp ((differentiable_const v0).add hwd)).mul ?_
    refine Differentiable.cexp ?_
    refine (differentiable_const _).mul ?_
    exact (innerSL ℂ v0).differentiable.comp hwd
  have hwn : ∀ z, ‖w z‖ = s⁻¹ * ‖z‖ := by
    intro z
    rw [hw]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hw0 : w 0 = 0 := by rw [hw]; simp
  have hexp2 : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have key : ∀ z, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Hf (v0 + w z) := by
    intro z
    have hz : ‖z‖ ^ 2 = q * Real.pi * ‖w z‖ ^ 2 := by
      rw [hwn, mul_pow, ← hs2, inv_pow]
      field_simp
    have hadd : ‖v0 + w z‖ ^ 2 = ‖v0‖ ^ 2 + 2 * (inner ℂ v0 (w z)).re + ‖w z‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ)]
      first | rfl | simp
    have hre : (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)).re =
        -(q * Real.pi) * (inner ℂ v0 (w z)).re := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have e1 : Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2) =
        Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0 + w z‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, hz, hadd]
      congr 1
      ring
    calc ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ‖F (v0 + w z)‖ ^ 2 *
            (Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2)) := by
          rw [hG]
          simp only [norm_mul, Complex.norm_exp, mul_pow, hre, hexp2]
          ring
      _ = _ := by rw [e1, hHf]; ring
  have hmem : ∀ z, v0 + w z ∈ Metric.closedBall v0 (ρ / s) ↔
      z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ := by
    intro z
    have hsub : v0 + w z - v0 = w z := by abel
    rw [Metric.mem_closedBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, hsub, sub_zero, hwn,
      div_eq_inv_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h (inv_pos.mpr hs0),
      fun h => mul_le_mul_of_nonneg_left h (inv_pos.mpr hs0).le⟩
  have hA : ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
      ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_const_mul]
    congr 1
    funext z
    by_cases hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ
    · rw [Set.indicator_of_mem hzb, Set.indicator_of_mem ((hmem z).2 hzb), key z]
    · have h2 : v0 + w z ∉ Metric.closedBall v0 (ρ / s) := fun h => hzb ((hmem z).1 h)
      simp [Set.indicator_apply, hzb, h2]
  have hC : ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) =
      s ^ (2 * Fintype.card ι) * ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u := by
    set h := (Metric.closedBall v0 (ρ / s)).indicator Hf
    have h1 : ∫ z, h (v0 + w z) = ∫ y, h (v0 + s⁻¹ • y) := by
      rw [hw]
      exact (eR.symm.measurePreserving).integral_comp eR.symm.toHomeomorph.measurableEmbedding
        (fun y => h (v0 + s⁻¹ • y))
    rw [h1, MeasureTheory.Measure.integral_comp_smul (μ := volume) (fun y => h (v0 + y)) s⁻¹,
      lemS_finrank, integral_add_left_eq_self, inv_pow, inv_inv, abs_of_pos (pow_pos hs0 _),
      smul_eq_mul]
  have L : ‖G 0‖ ^ 2 ≤ 2 / Real.pi ^ Fintype.card ι *
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
        ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := sq_norm_zero_le_gauss_ball G hGd
  have hG0 : G 0 = F v0 := by rw [hG]; simp [hw0]
  have hsn : s ^ (2 * Fintype.card ι) = (q * Real.pi) ^ Fintype.card ι := by rw [pow_mul, hs2]
  have hJ : ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u =
      ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
    rw [integral_indicator measurableSet_closedBall, hHf]
  rw [hA, hC, hG0, hsn, hJ] at L
  have hE : Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hpi : Real.pi ^ Fintype.card ι ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  set J := ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)
  calc ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)
      ≤ 2 / Real.pi ^ Fintype.card ι *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ((q * Real.pi) ^ Fintype.card ι * J)) *
          Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) := mul_le_mul_of_nonneg_right L (Real.exp_pos _).le
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J * (Real.pi ^ Fintype.card ι / Real.pi ^ Fintype.card ι) *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)) := by
        rw [mul_pow]; ring
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J := by rw [hE, div_self hpi]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

