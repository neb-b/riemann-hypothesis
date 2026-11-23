module

public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlaceRankTwoOne
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
section
open MeasureTheory Matrix Topology Metric Kronecker

noncomputable section

namespace Formalism.REAL

lemma stdBasis_repr_apply (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr x (i, j) = x i j := by
  simp [Matrix.stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]

lemma det_mulLeft_complex {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ g) = g.det ^ n := by
  classical
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  have : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n))
      (LinearMap.mulLeft ℂ g) = g ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_repr_apply]
    simp only [Matrix.stdBasis_eq_single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      LinearMap.mulLeft_apply, Matrix.mul_apply, Matrix.single_apply]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_kronecker]
  simp

lemma det_leftMul_restrictScalars {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) = Complex.normSq g.det ^ n := by
  rw [LinearMap.det_restrictScalars, det_mulLeft_complex, map_pow, Algebra.norm_complex_apply]

lemma normSq_det_indefinite_unitary {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det ≠ 0 := by
    have := congrArg Matrix.det (Jm_mul_self ε)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det - 1) * (Jm ε).det = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h3 | h3
    · linear_combination h3
    · exact absurd h3 hJ
  rw [Complex.star_def] at h2
  have h3 : (Complex.normSq g.det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

abbrev MatrixCoordinates (n : ℕ) := Fin n → Fin n → ℂ

def matrixCoordinatesEquiv (n : ℕ) : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := Matrix.ofLinearEquiv ℝ

def leftMulReal {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : MatrixCoordinates n →ₗ[ℝ] MatrixCoordinates n :=
  ((matrixCoordinatesEquiv n).symm : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MatrixCoordinates n) ∘ₗ
    ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) ∘ₗ
    ((matrixCoordinatesEquiv n : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      MatrixCoordinates n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)

lemma leftMulReal_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    leftMulReal g x = Matrix.of.symm (g * Matrix.of x) := rfl

lemma det_leftMulReal_eq_one {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    LinearMap.det (leftMulReal g) = 1 := by
  unfold leftMulReal
  have := LinearMap.det_conj ((LinearMap.mulLeft ℂ g).restrictScalars ℝ)
    (matrixCoordinatesEquiv n).symm
  rw [LinearEquiv.symm_symm] at this
  rw [this, det_leftMul_restrictScalars, normSq_det_indefinite_unitary hg, one_pow]

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma frobenius_eq_norm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hs A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [hs]

lemma sqrt_frobenius_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma sqrt_frobenius_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A * B)) ≤ Real.sqrt (hs A) * Real.sqrt (hs B) := by
  simp only [sqrt_frobenius_eq_norm]; exact Matrix.frobenius_norm_mul A B

lemma sqrt_frobenius_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A + B)) ≤ Real.sqrt (hs A) + Real.sqrt (hs B) := by
  simp only [sqrt_frobenius_eq_norm]; exact norm_add_le A B

end frob

lemma of_leftMulReal_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    Matrix.of (leftMulReal A x) = A * Matrix.of x := by
  rw [leftMulReal_apply, Equiv.apply_symm_apply]

lemma determinant_character_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) :
    coeMatrixAlt ε (g * h) = coeMatrixAlt ε g * coeMatrixAlt ε h := rfl

lemma determinant_character_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) :
    coeMatrixAlt ε g * coeMatrixAlt ε g⁻¹ = 1 := by
  rw [← determinant_character_mul, mul_inv_cancel]; rfl

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma norm_one_matrix_eq_sqrt (n : ℕ) : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_frobenius_eq_norm, f1auxiliary_hs_one]

lemma norm_sub_one_lt_half {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u - 1‖ < 1 / 2 := by
  rw [frobenius_eq_norm_sq] at hu
  nlinarith [norm_nonneg (u - 1)]

lemma norm_le_of_near_one {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u‖ ≤ Real.sqrt n + 1 / 2 := by
  have h1 := norm_sub_one_lt_half hu
  have h2 : ‖u‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_one_matrix_eq_sqrt] at h2
  linarith

lemma frobenius_bound_of_mul_near_one {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4)
    (hv : hs (v - 1) < 1 / 4) (h : k * u = v) : hs k ≤ (2 * Real.sqrt n + 1) ^ 2 := by
  have e : k = v + k * (1 - u) := by rw [Matrix.mul_sub, Matrix.mul_one, h]; abel
  have h1 : ‖k‖ ≤ ‖v‖ + ‖k‖ * ‖1 - u‖ := by
    calc ‖k‖ = ‖v + k * (1 - u)‖ := by rw [← e]
      _ ≤ ‖v‖ + ‖k * (1 - u)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  rw [norm_sub_rev] at h1
  have h2 := norm_sub_one_lt_half hu
  have h3 := norm_le_of_near_one hv
  have hk : ‖k‖ ≤ 2 * Real.sqrt n + 1 := by nlinarith [norm_nonneg k, norm_nonneg (u - 1)]
  rw [frobenius_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hk 2

lemma norm_entry_mul_near_one_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) < 1 / 4) (i j : Fin n) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hg' : ‖g‖ ≤ R := by
    rw [frobenius_eq_norm_sq] at hg
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu' := norm_le_of_near_one hu
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1 / 2) := by gcongr
    _ ≤ R * (Real.sqrt n + 1) := by gcongr; norm_num

end frob

theorem ball_finite_measure_holds : BallFinite := by
  intro n ε R
  have hc : IsCompact {g : UJ ε | hsG g ≤ R} := by
    have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 R)
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  exact hc.measure_lt_top

theorem volume_growth : VolGrowth :=
  _root_.UpperTheory.Reformulated.B.placeRankTwoOne.volume_growth

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
section
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.REAL

def indefiniteUnitaryMk {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) : UJ ε :=
  ⟨⟨m, Jm ε * mᴴ * Jm ε, (indefinite_unitary_inv_closed n ε m h).1, (indefinite_unitary_inv_closed n ε m h).2⟩, h⟩

lemma indefiniteUnitaryMk_val {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) :
    (((indefiniteUnitaryMk ε m h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = m := rfl

lemma indefinite_unitary_ext {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε}
    (e : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) : g = h :=
  Subtype.ext (Units.ext e)

abbrev modularCharacterAlt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : ℝ≥0 := Measure.modularCharacterFun g

lemma map_mul_right_haar_modular_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muG ε) = modularCharacterAlt ε g • muG ε := by
  rw [modularCharacterAlt, Measure.modularCharacterFun_eq_haarScalarFactor (muG ε) g]
  exact Measure.isMulLeftInvariant_eq_smul _ _

lemma modularCharacter_mul {n : ℕ} (ε : Fin n → Bool) (g h : UJ ε) :
    modularCharacterAlt ε (g * h) = modularCharacterAlt ε g * modularCharacterAlt ε h :=
  Measure.modularCharacterFun_map_mul g h

lemma modularCharacter_one {n : ℕ} (ε : Fin n → Bool) : modularCharacterAlt ε 1 = 1 :=
  Measure.modularCharacterFun_map_one

lemma continuous_frobenius_on_group {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG (ε := ε)) :=
  continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)

lemma frobenius_ball_compact_pos_finite {n : ℕ} (ε : Fin n → Bool) :
    IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧ 0 < muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧
      muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} := by
    have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 ((n : ℝ) + 1))
    convert h using 1
    ext g
    exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
  refine ⟨hc, ?_, hc.measure_lt_top⟩
  have hU : IsOpen {g : UJ ε | hsG g < (n : ℝ) + 1} :=
    isOpen_lt (continuous_frobenius_on_group ε) continuous_const
  have h1 : (1 : UJ ε) ∈ {g : UJ ε | hsG g < (n : ℝ) + 1} := by
    show hs (1 : Matrix (Fin n) (Fin n) ℂ) < (n : ℝ) + 1
    rw [f1auxiliary_hs_one]; linarith
  exact (hU.measure_pos (muG ε) ⟨1, h1⟩).trans_le
    (measure_mono fun g (hg : hsG g < (n : ℝ) + 1) => hg.le)

lemma modularCharacter_eq_one_on_compact {n : ℕ} (ε : Fin n → Bool) (g : UJ ε)
    (hk : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    modularCharacterAlt ε g = 1 := by
  obtain ⟨hc, hpos, hfin⟩ := frobenius_ball_compact_pos_finite ε
  set B := {g : UJ ε | hsG g ≤ (n : ℝ) + 1} with hB
  have hBm : MeasurableSet B := hc.isClosed.measurableSet
  have hpre : (fun x => x * g) ⁻¹' B = B := by
    ext x
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq, hsG, Subgroup.coe_mul, Units.val_mul]
    rw [((hermitian_small_ball n ε).2 _ _ hk).1]
  have h1 := map_mul_right_haar_modular_alt ε g
  have h2 : (Measure.map (fun x => x * g) (muG ε)) B = muG ε B := by
    rw [Measure.map_apply (measurable_mul_const g) hBm, hpre]
  rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modularCharacterAlt ε g : ℝ≥0∞)) * muG ε B = 1 * muG ε B := by rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos.ne' hfin.ne] at h3
  exact_mod_cast h3

lemma signature_mem_indefinite_unitary {n : ℕ} (ε : Fin n → Bool) : inUJ ε (Jm ε) :=
  (maximal_compact_facts n ε).1 _ (maximal_compact_facts n ε).2.2.1

lemma modularCharacter_eq_one_on_exp_hermitian {n : ℕ} (ε : Fin n → Bool) (p : UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X)
    (hp : ((p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X) :
    modularCharacterAlt ε p = 1 := by
  set j := indefiniteUnitaryMk ε (Jm ε) (signature_mem_indefinite_unitary ε) with hj
  have hDj : modularCharacterAlt ε j = 1 := modularCharacter_eq_one_on_compact ε j (maximal_compact_facts n ε).2.2.1
  have hherm : (NormedSpace.exp X)ᴴ = NormedSpace.exp X :=
    exp_conjTranspose_of_hermitian (((parabolic_character_holds n ε X).1.mp hX).1)
  have hconj : j * p * j = p⁻¹ := by
    apply indefinite_unitary_ext
    have hinv := coeMatrix_inv_eq ε p
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [hinv, hj, indefiniteUnitaryMk_val]
    show Jm ε * _ * Jm ε = Jm ε * (coeMatrixAlt ε p)ᴴ * Jm ε
    rw [show coeMatrixAlt ε p = NormedSpace.exp X from hp, hp, hherm]
  have h1 : modularCharacterAlt ε p⁻¹ = modularCharacterAlt ε p := by
    rw [← hconj, modularCharacter_mul, modularCharacter_mul, hDj, one_mul, mul_one]
  have h2 : modularCharacterAlt ε p * modularCharacterAlt ε p = 1 := by
    rw [← modularCharacter_one ε, ← mul_inv_cancel p, modularCharacter_mul, h1]
  have h3 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) * (modularCharacterAlt ε p : ℝ) = 1 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (modularCharacterAlt ε p : ℝ) := (modularCharacterAlt ε p).2
  have h5 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

lemma modularCharacter_eq_one_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : modularCharacterAlt ε g = 1 := by
  have hgU : inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k, X, hk, hX, hg⟩ := (polar_decomposition_holds n ε).1 _ hgU
  have hkU : inUJ ε k := (maximal_compact_facts n ε).1 k hk
  have hEU : inUJ ε (NormedSpace.exp X) := by
    have h := exp_indefinite_unitary_holds n ε X hX.1 1
    rwa [Complex.ofReal_one, one_smul] at h
  have hdec : g = indefiniteUnitaryMk ε k hkU * indefiniteUnitaryMk ε _ hEU := by
    apply indefinite_unitary_ext
    rw [Subgroup.coe_mul, Units.val_mul, indefiniteUnitaryMk_val, indefiniteUnitaryMk_val]
    exact hg
  have hk' : (((indefiniteUnitaryMk ε k hkU : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ Kset ε := hk
  rw [hdec, modularCharacter_mul, modularCharacter_eq_one_on_compact ε _ hk', modularCharacter_eq_one_on_exp_hermitian ε _ X hX (indefiniteUnitaryMk_val ε _ hEU), one_mul]

theorem indefinite_unitary_unimodular : Unimodular := by
  intro n ε g
  rw [map_mul_right_haar_modular_alt, modularCharacter_eq_one_alt, one_smul]

theorem invInvariant_of (h : Unimodular) : InvInvariant :=
  _root_.UpperTheory.Reformulated.B.InvolutionInvariants.invInvariant_of h

end Formalism.REAL
end
end

