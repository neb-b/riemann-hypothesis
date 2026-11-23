module

public import Mathlib

@[expose] public section

open Module Matrix
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


variable (𝕜) in
def gramVol (v : ι → V) : ℝ := √(RCLike.re (gram 𝕜 v).det)

theorem gramVol_nonneg (v : ι → V) : 0 ≤ gramVol 𝕜 v := Real.sqrt_nonneg _

theorem gramVol_sq (v : ι → V) : ((gramVol 𝕜 v : ℝ) : 𝕜) ^ 2 = (gram 𝕜 v).det := by
  have h := (posSemidef_gram 𝕜 v).det_nonneg
  rw [RCLike.nonneg_iff] at h
  rw [← RCLike.ofReal_pow, gramVol, Real.sq_sqrt h.1]
  apply RCLike.ext <;> simp [h.2]

theorem gramVol_eq_of_sq {v : ι → V} {r : ℝ} (hr : 0 ≤ r) (h : (r : 𝕜) ^ 2 = (gram 𝕜 v).det) :
    gramVol 𝕜 v = r := by
  rw [← gramVol_sq] at h
  have : r ^ 2 = gramVol 𝕜 v ^ 2 := by exact_mod_cast h
  exact ((sq_eq_sq₀ hr (gramVol_nonneg v)).mp this).symm

theorem gramVol_of_orthonormal {v : ι → V} (hv : Orthonormal 𝕜 v) : gramVol 𝕜 v = 1 :=
  gramVol_eq_of_sq zero_le_one (by simp [gram_eq_one_iff_orthonormal.mpr hv])

theorem gramVol_of_pairwise_orthogonal {v : ι → V}
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) : gramVol 𝕜 v = ∏ i, ‖v i‖ := by
  refine gramVol_eq_of_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  have : gram 𝕜 v = diagonal fun i => ((‖v i‖ : 𝕜) ^ 2) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [inner_self_eq_norm_sq_to_K]
    · simp [h, hv h]
  rw [this, det_diagonal]
  push_cast
  rw [Finset.prod_pow]

@[simp] theorem gramVol_unique [Unique ι] (v : ι → V) : gramVol 𝕜 v = ‖v default‖ := by
  rw [gramVol_of_pairwise_orthogonal (Subsingleton.pairwise), Fintype.prod_unique]


omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem gram_sum_smul (v : ι → V) (Y : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, Y i j • v i) = Yᴴ * gram 𝕜 v * Y := by
  ext a b
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gramVol_sum_smul (v : ι → V) (Y : Matrix ι ι 𝕜) :
    gramVol 𝕜 (fun j => ∑ i, Y i j • v i) = ‖Y.det‖ * gramVol 𝕜 v := by
  refine gramVol_eq_of_sq (mul_nonneg (norm_nonneg _) (gramVol_nonneg v)) ?_
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, ← gramVol_sq, RCLike.star_def]
  push_cast
  rw [mul_pow, ← RCLike.conj_mul]
  ring

theorem gramVol_eq_norm_det (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    gramVol 𝕜 v = ‖(b.toBasis.toMatrix v).det‖ := by
  have h := gramVol_sum_smul (b : ι → V) (b.toBasis.toMatrix v)
  rw [gramVol_of_orthonormal b.orthonormal, mul_one] at h
  rw [← h]
  congr 1
  ext j
  simpa [Basis.toMatrix_apply] using (b.sum_repr (v j)).symm

theorem norm_det_inner [FiniteDimensional 𝕜 V] (hι : Fintype.card ι = finrank 𝕜 V)
    (w v : ι → V) :
    ‖(Matrix.of fun i j => ⟪w i, v j⟫_𝕜).det‖ = gramVol 𝕜 w * gramVol 𝕜 v := by
  let b : OrthonormalBasis ι 𝕜 V :=
    (stdOrthonormalBasis 𝕜 V).reindex (Fintype.equivFinOfCardEq hι).symm
  have : (Matrix.of fun i j => ⟪w i, v j⟫_𝕜) = (b.toBasis.toMatrix w)ᴴ * b.toBasis.toMatrix v := by
    ext i j
    simp [Matrix.mul_apply, Basis.toMatrix_apply, b.repr_apply_apply, b.sum_inner_mul_inner]
  rw [this, det_mul, det_conjTranspose, norm_mul, norm_star, gramVol_eq_norm_det b,
    gramVol_eq_norm_det b]

theorem gramVol_mul_gramVol_of_biorthogonal [FiniteDimensional 𝕜 V]
    (hι : Fintype.card ι = finrank 𝕜 V) {w v : ι → V}
    (h : ∀ i j, ⟪w i, v j⟫_𝕜 = if i = j then 1 else 0) : gramVol 𝕜 w * gramVol 𝕜 v = 1 := by
  rw [← norm_det_inner hι]
  have : (Matrix.of fun i j => ⟪w i, v j⟫_𝕜) = 1 := by
    ext i j; simp [h, Matrix.one_apply]
  simp [this]

section NormDet

variable [FiniteDimensional 𝕜 V]

theorem normDet_eq_gramVol (T : V →ₗ[𝕜] W) (b : OrthonormalBasis ι 𝕜 V) :
    T.normDet = gramVol 𝕜 (fun i => T (b i)) :=
  (gramVol_eq_of_sq T.normDet_nonneg (by simpa using T.normDet_sq_eq_det_gram b)).symm

theorem normDet_mul_normDet_of_inner_eq [FiniteDimensional 𝕜 W] {S T : V →ₗ[𝕜] W}
    (h : finrank 𝕜 V = finrank 𝕜 W) (hST : ∀ x y, ⟪S x, T y⟫_𝕜 = ⟪x, y⟫_𝕜) :
    S.normDet * T.normDet = 1 := by
  let b := stdOrthonormalBasis 𝕜 V
  rw [normDet_eq_gramVol _ b, normDet_eq_gramVol _ b]
  refine gramVol_mul_gramVol_of_biorthogonal (by simpa using h) fun i j => ?_
  rw [hST, orthonormal_iff_ite.mp b.orthonormal]

abbrev detNorm (T : V ≃ₗ[𝕜] W) : ℝ := (T : V →ₗ[𝕜] W).normDet

variable [FiniteDimensional 𝕜 W]

def invAdjoint (T : V ≃ₗ[𝕜] W) : V ≃ₗ[𝕜] W :=
  LinearEquiv.ofLinearMap (LinearMap.adjoint (T.symm : W →ₗ[𝕜] V)) (LinearMap.adjoint (T : V →ₗ[𝕜] W))
    (by rw [← LinearMap.adjoint_comp]; simp) (by rw [← LinearMap.adjoint_comp]; simp)

theorem inner_invAdjoint_apply (T : V ≃ₗ[𝕜] W) (x y : V) :
    ⟪invAdjoint T x, T y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  change ⟪LinearMap.adjoint (T.symm : W →ₗ[𝕜] V) x, T y⟫_𝕜 = _
  rw [LinearMap.adjoint_inner_left]; simp

theorem detNorm_invAdjoint (T : V ≃ₗ[𝕜] W) : detNorm (invAdjoint T) = (detNorm T)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (normDet_mul_normDet_of_inner_eq T.finrank_eq (inner_invAdjoint_apply T))

end NormDet

section Dual

open InnerProductSpace

variable [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 X]



end Dual

end GlobalTheory
