module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LeftMulMapEqTransposeConj
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem matrix_space_volume_isAddHaar (N : ℕ) : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := by
  haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance
  haveI hS : SigmaFinite (volume : Measure ℂ) := by infer_instance
  haveI h1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  haveI hS1 : SigmaFinite (volume : Measure (Fin N → ℂ)) := by infer_instance
  rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _

def leftMulLinearMap (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (g * Matrix.of Z)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

def rightMulLinear (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (Matrix.of Z * g)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]; ring_nf

theorem right_mul_map_eq_pi_toLin (g : Matrix (Fin N) (Fin N) ℂ) :
    rightMulLinear g = LinearMap.pi (fun i : Fin N => (Matrix.toLin' gᵀ).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro Z; funext i j
  simp [rightMulLinear, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_right_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (rightMulLinear g) = g.det ^ N := by
  rw [right_mul_map_eq_pi_toLin, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

def transposeLinearEquivAlt : (Fin N → Fin N → ℂ) ≃ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z i j := Z j i
  invFun Z i j := Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem left_mul_map_eq_transpose_conj (g : Matrix (Fin N) (Fin N) ℂ) :
    leftMulLinearMap g = (transposeLinearEquivAlt (N := N)).toLinearMap ∘ₗ rightMulLinear gᵀ ∘ₗ
      (transposeLinearEquivAlt (N := N)).symm.toLinearMap := by
  apply LinearMap.ext; intro Z; funext i j
  show (∑ k, g i k * Z k j) = ∑ k, Z k j * g i k
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem det_left_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (leftMulLinearMap g) = g.det ^ N := by
  rw [left_mul_map_eq_transpose_conj, LinearMap.det_conj, det_right_mul_map_eq_det_pow, Matrix.det_transpose]

theorem real_det_restrictScalars (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ)
    (hf : LinearMap.det f = d ^ N) :
    LinearMap.det (f.restrictScalars ℝ) = (‖d‖ ^ 2) ^ N := by
  rw [LinearMap.det_restrictScalars, hf, map_pow, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

theorem zpow_neg_two_mul_eq_inv_sq_pow (x : ℝ) : x ^ (-(2 * (N : ℤ))) = ((x ^ 2) ^ N)⁻¹ := by
  rw [_root_.zpow_neg, ← pow_mul, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem map_volume_of_det_eq_pow (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ) (hd : d ≠ 0)
    (hf : LinearMap.det f = d ^ N) :
    Measure.map (f.restrictScalars ℝ) volume = ENNReal.ofReal (‖d‖ ^ (-(2 * (N : ℤ)))) • volume := by
  have hdet := real_det_restrictScalars f d hf
  have hne : LinearMap.det (f.restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))
  haveI := matrix_space_volume_isAddHaar N
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, hdet, zpow_neg_two_mul_eq_inv_sq_pow,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))]

private theorem fdV0_det_cont_lemma (N : ℕ) :
    Continuous (fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det) :=
  Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))

theorem measurable_gl_density : Measurable (gmDens N) := by
  have h : gmDens N = fun Z => ENNReal.ofReal (((‖(Matrix.of Z).det‖ ^ 2) ^ N)⁻¹) := by
    funext Z; simp only [gmDens, zpow_neg_two_mul_eq_inv_sq_pow]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    (((fdV0_det_cont_lemma N).norm.measurable.pow_const 2).pow_const N).inv

theorem gl_density_left_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (g * Matrix.of Z)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem gl_density_right_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (Matrix.of Z * g)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, mul_comm (Matrix.of Z).det, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem map_gaussian_measure_eq {φ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)} (hφ : Measurable φ) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hmap : Measure.map φ volume = c • volume)
    (hd : ∀ Z, gmDens N (φ Z) = c * gmDens N Z) : Measure.map φ (gmMeas N) = gmMeas N := by
  ext s hs
  have hD := measurable_gl_density (N := N)
  have key : ∀ Z, gmDens N Z = c⁻¹ * gmDens N (φ Z) := by
    intro Z; rw [hd, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have h1 : ∫⁻ Z in φ ⁻¹' s, gmDens N Z = c⁻¹ * ∫⁻ Z in φ ⁻¹' s, gmDens N (φ Z) := by
    rw [← lintegral_const_mul c⁻¹ (f := fun Z => gmDens N (φ Z)) (hD.comp hφ)]
    exact lintegral_congr fun Z => key Z
  simp only [gmMeas]
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs, h1,
    ← setLIntegral_map hs hD hφ, hmap, Measure.restrict_smul, lintegral_smul_measure]
  try simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem ofReal_norm_det_zpow_ne_zero (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (zpow_pos (norm_pos_iff.mpr hg) _)).ne'

theorem map_volume_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (leftMulLinearMap g) g.det hg (det_left_mul_map_eq_det_pow g)

theorem map_volume_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (rightMulLinear g) g.det hg (det_right_mul_map_eq_det_pow g)

theorem gmMeas_map_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) :=
    (leftMulLinearMap g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_left g hg)
    (gl_density_left_mul g)

theorem gmMeas_map_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) :=
    (rightMulLinear g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_right g hg)
    (gl_density_right_mul g)

theorem gmMeas_compact_lt_top (K : Set (Fin N → Fin N → ℂ)) (hK : IsCompact K)
    (hK0 : ∀ Z ∈ K, (Matrix.of Z).det ≠ 0) : gmMeas N K < ⊤ := by
  have hcont : ContinuousOn
      (fun Z : Fin N → Fin N → ℂ => ‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ)))) K :=
    ((fdV0_det_cont_lemma N).norm.continuousOn).zpow₀ _
      fun Z hZ => Or.inl (norm_ne_zero_iff.mpr (hK0 Z hZ))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hDle : ∀ Z ∈ K, gmDens N Z ≤ ENNReal.ofReal C := fun Z hZ =>
    ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC Z hZ))
  simp only [gmMeas]
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ Z in K, gmDens N Z ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hK.measurableSet hDle)
    _ = ENNReal.ofReal C * volume K := setLIntegral_const K _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaarA
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def IsUpT (M : Matrix (Fin N) (Fin N) ℂ) : Prop := ∀ a b, b < a → M a b = 0

theorem upMat_isUpT (t : TriCo N) : IsUpT (upMat t) := by
  intro a b h
  simp [upMat, ne_of_gt h, not_lt.mpr h.le]

theorem upMat_diag (t : TriCo N) (a : Fin N) : upMat t a a = ((t.1 a : ℝ) : ℂ) := by
  simp [upMat]

theorem upMat_lt (t : TriCo N) {a b : Fin N} (h : a < b) : upMat t a b = t.2 ⟨(a, b), h⟩ := by
  simp [upMat, h.ne, h]

theorem isUpT_mul {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) : IsUpT (A * B) := by
  intro a b h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k a with hk | hk
  · rw [hA a k hk, zero_mul]
  · rw [hB k b (lt_of_lt_of_le h hk), mul_zero]

theorem isUpT_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) (a : Fin N) :
    (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hA a k hk, zero_mul]
    · rw [hB k a hk, mul_zero]
  · simp

theorem upMat_triCoOf_of {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsUpT M) (hd : ∀ a, (M a a).im = 0) :
    upMat (triCoOf M) = M := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h]; rfl
  · subst h; rw [upMat_diag]; simp only [triCoOf]
    exact Complex.ext (by simp) (by simp [hd])
  · rw [upMat_isUpT _ a b h, hM a b h]

theorem triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  ext j
  · simp [triCoOf, upMat]
  · simp only [triCoOf]; rw [upMat_lt _ j.2]

theorem upMat_add (s t : TriCo N) : upMat (s + t) = upMat s + upMat t := by
  ext a b; simp only [upMat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp

theorem upMat_smul (c : ℝ) (t : TriCo N) : upMat (c • t) = c • upMat t := by
  ext a b; simp only [upMat, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

theorem triCoOf_add (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A + B) = triCoOf A + triCoOf B := by
  ext j <;> simp [triCoOf]

theorem triCoOf_smul (c : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) : triCoOf (c • A) = c • triCoOf A := by
  ext j <;> simp [triCoOf]

theorem upMat_injective : Function.Injective (upMat (N := N)) := by
  intro s t h
  rw [← triCoOf_upMat s, ← triCoOf_upMat t, h]

def rmulL (B : Matrix (Fin N) (Fin N) ℂ) : TriCo N →ₗ[ℝ] TriCo N where
  toFun t := triCoOf (upMat t * B)
  map_add' s t := by rw [upMat_add, Matrix.add_mul, triCoOf_add]
  map_smul' c t := by rw [upMat_smul, Matrix.smul_mul, triCoOf_smul]; rfl

theorem rmulL_apply (B : Matrix (Fin N) (Fin N) ℂ) (t : TriCo N) :
    rmulL B t = triCoOf (upMat t * B) := rfl

theorem triCoOf_sub (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A - B) = triCoOf A - triCoOf B := by
  ext j <;> simp [triCoOf]

theorem upMat_zero : upMat (0 : TriCo N) = 0 := by
  ext a b; simp only [upMat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]; split_ifs <;> simp

theorem upMat_triCoOf_eq_zero {X : Matrix (Fin N) (Fin N) ℂ} {a b : Fin N} (h : X a b = 0) :
    upMat (triCoOf X) a b = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [upMat_lt _ hab]; exact h
  · subst hab; rw [upMat_diag]; simp [triCoOf, h]
  · exact upMat_isUpT _ a b hab

theorem det_rmulL_unip (U : Matrix (Fin N) (Fin N) ℂ) (hU : ∀ c b, b ≤ c → (1 - U) c b = 0) :
    LinearMap.det (rmulL U) = 1 := by
  set Nl : Module.End ℝ (TriCo N) := 1 - rmulL U with hNl
  have hN : ∀ s, Nl s = triCoOf (upMat s * (1 - U)) := by
    intro s
    rw [Matrix.mul_sub, Matrix.mul_one, triCoOf_sub, triCoOf_upMat, hNl]
    rfl
  have hpow : ∀ k s, ∀ a b : Fin N, (b : ℕ) < a + k → upMat ((Nl ^ k) s) a b = 0 := by
    intro k
    induction k with
    | zero => intro s a b h; exact upMat_isUpT _ a b (by simpa using h)
    | succ k ih =>
      intro s a b h
      rw [pow_succ', Module.End.mul_apply, hN]
      apply upMat_triCoOf_eq_zero
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : (c : ℕ) < a + k
      · rw [ih s a c hc, zero_mul]
      · rw [hU c b (by rw [Fin.le_def]; omega), mul_zero]
  have hnil : IsNilpotent Nl := by
    refine ⟨N, LinearMap.ext fun s => ?_⟩
    apply upMat_injective
    rw [LinearMap.zero_apply, upMat_zero]
    ext a b
    exact hpow N s a b (by omega)
  have h1 := LinearMap.eval_charpoly Nl 1
  rw [hnil.charpoly_eq_X_pow_finrank] at h1
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h1
  rw [h1, hNl, sub_sub_cancel]

def scaleL (d : Fin N → ℝ) : TriCo N →ₗ[ℝ] TriCo N :=
  LinearMap.prodMap (LinearMap.pi fun j => (d j • LinearMap.id).comp (LinearMap.proj j))
    (LinearMap.pi fun ab : {ab : Fin N × Fin N // ab.1 < ab.2} =>
      ((d ab.1.2 • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj ab))

theorem scaleL_triCoOf (d : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    scaleL d (triCoOf X) = triCoOf (X * Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) := by
  ext j
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, mul_comm]
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, Complex.real_smul, mul_comm]

theorem prod_subtype_snd (f : Fin N → ℝ) :
    ∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, f ab.1.2 = ∏ j : Fin N, f j ^ (j : ℕ) := by
  rw [← Finset.prod_subtype (univ.filter fun ab : Fin N × Fin N => ab.1 < ab.2) (by simp)
    (fun ab => f ab.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]
  show ∏ a ∈ univ.filter (fun a : Fin N => a < j), f j = _
  rw [Finset.prod_const]
  have : (univ.filter fun a : Fin N => a < j) = Iio j := by ext; simp
  rw [this, Fin.card_Iio]

theorem det_scaleL (d : Fin N → ℝ) :
    LinearMap.det (scaleL d) = ∏ j : Fin N, d j ^ (2 * (j : ℕ) + 1) := by
  rw [scaleL, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one,
    Complex.finrank_real_complex]
  rw [prod_subtype_snd (fun j => d j ^ 2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

def unipOf (t0 : TriCo N) : TriCo N := (fun _ => 1, fun ab => t0.2 ab / ((t0.1 ab.1.2 : ℝ) : ℂ))

theorem upMat_eq_unip_mul (t0 : TriCo N) (h0 : ∀ j, t0.1 j ≠ 0) :
    upMat t0 = upMat (unipOf t0) * Matrix.diagonal fun j => ((t0.1 j : ℝ) : ℂ) := by
  ext a b
  rw [Matrix.mul_diagonal]
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h, upMat_lt _ h]
    have : ((t0.1 b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0 b
    simp only [unipOf]
    field_simp
  · subst h; rw [upMat_diag, upMat_diag]; simp [unipOf]
  · rw [upMat_isUpT _ a b h, upMat_isUpT _ a b h, zero_mul]

theorem det_rmulL_upMat (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    LinearMap.det (rmulL (upMat t0)) = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := by
  have hne : ∀ j, t0.1 j ≠ 0 := fun j => (h0 j).ne'
  have hc : rmulL (upMat t0) = scaleL t0.1 ∘ₗ rmulL (upMat (unipOf t0)) := by
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.comp_apply, rmulL_apply, rmulL_apply, scaleL_triCoOf, upMat_eq_unip_mul t0 hne,
      Matrix.mul_assoc]
  rw [hc, LinearMap.det_comp, det_scaleL, det_rmulL_unip, mul_one]
  intro c b hbc
  rcases lt_or_eq_of_le hbc with h | h
  · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt h), upMat_isUpT _ c b h, sub_zero]
  · subst h; rw [Matrix.sub_apply, Matrix.one_apply_eq, upMat_diag]; simp [unipOf]

theorem upMat_triCoOf_mul' (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU := isUpT_mul (upMat_isUpT t) (upMat_isUpT t0)
  have hd : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := fun a => by
    rw [isUpT_mul_diag (upMat_isUpT t) (upMat_isUpT t0), upMat_diag, upMat_diag]; push_cast; ring
  refine ⟨upMat_triCoOf_of hU fun a => by rw [hd]; simp, fun j => ?_⟩
  simp only [triCoOf]; rw [hd]; simp

theorem triDens_measurable : Measurable (triDens (N := N)) := by unfold triDens; fun_prop

theorem triDens_rmulL (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    triDens t = ENNReal.ofReal (∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1)) *
      triDens (rmulL (upMat t0) t) := by
  have h2 := (upMat_triCoOf_mul' t t0).2
  unfold triDens
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => pow_nonneg (h0 j).le _)]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rmulL_apply, h2 j, mul_zpow]
  have hne : t0.1 j ≠ 0 := (h0 j).ne'
  have : t0.1 j ^ (2 * (j : ℕ) + 1) * t0.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hne]; push_cast; simp
  rw [mul_left_comm, this, mul_one]

theorem rmulL_mem_triPos (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    rmulL (upMat t0) t ∈ triPos N ↔ t ∈ triPos N := by
  simp only [triPos, Set.mem_ofPred_eq, rmulL_apply, (upMat_triCoOf_mul' t t0).2]
  exact forall_congr' fun j => mul_pos_iff_of_pos_right (h0 j)

end ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUMeasurableSetTriPos
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_pos' (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

theorem volU_skMat_conjTranspose (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  simp only [conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt.2 h.le]
  · simp
  · simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem volU_exp_inUJ (x : UCo N) :
    inUJ (fun _ : Fin N => true) (NormedSpace.exp (skMat x)) := by
  have hJ : Jm (fun _ : Fin N => true) = 1 := by simp [Jm]
  unfold inUJ
  rw [hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose,
    ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem volU_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop
  · simp only [if_true]
    fun_prop
  · simp only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop

theorem volU_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have h1 : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · simpa [skMat, Complex.I_ne_zero] using h1 a a
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    simpa [skMat, hab.ne', hab] using h1 a b

theorem volU_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp [skMat]

theorem volU_exp_injOn : ∃ δ > 0, Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x))
    (Metric.ball 0 δ) := by
  obtain ⟨ℓ, -, -, hℓ⟩ := lcA_exists_log (n := N)
  have hc : Tendsto (skMat (N := N)) (𝓝 0) (𝓝 0) := by
    have := (volU_continuous_skMat (N := N)).tendsto 0
    rwa [volU_skMat_zero] at this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hc.eventually hℓ)
  refine ⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩
  have ex := hδ' (Metric.mem_ball.1 hx)
  have ey := hδ' (Metric.mem_ball.1 hy)
  simp only at hxy ex ey
  rw [← ex, ← ey, hxy]

def volUOne (N : ℕ) : TriCo N := (fun _ => 1, 0)

theorem volU_upMat_add (t : TriCo N) : upMat (t + volUOne N) = 1 + upMat t := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [upMat, volUOne, add_comm]
  · simp [upMat, volUOne, h]

theorem volU_qrWt_one : qrWt (volUOne N) = 1 := by
  simp [qrWt, volUOne]

theorem volU_continuous_qrWt : Continuous (qrWt (N := N)) :=
  continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _

theorem volU_ball_sub_triPos {ρ : ℝ} (hρ : ρ ≤ 1) : Metric.ball (volUOne N) ρ ⊆ triPos N := by
  intro t ht j
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖ :=
    (norm_le_pi_norm _ j).trans (norm_fst_le _)
  have h2 : (t - volUOne N).1 j = t.1 j - 1 := by simp [volUOne]
  rw [h2, Real.norm_eq_abs] at h1
  linarith [neg_le_abs (t.1 j - 1)]

theorem volU_measurableSet_triPos : MeasurableSet (triPos N) := by
  simp only [triPos, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

end ReciprocityTheory.ChartRestriction.DS
end
end

