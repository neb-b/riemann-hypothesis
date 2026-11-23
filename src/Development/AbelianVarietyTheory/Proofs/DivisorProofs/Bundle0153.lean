module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpoly
section
noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing

namespace GlobalTheory.MaxOrder

theorem exists_eq_uniformizer_smul {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (P₀ : O[X])
    (hP : IsCoprime P₀ (derivative P₀)) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : γ.charpoly = P₀.map (algebraMap O K)) (π : O) (hπ : Irreducible π)
    (y : Matrix (Fin n) (Fin n) K) (hy : IsIntegral O y) (N : ℕ) (hN : 1 ≤ N) (f : O[X])
    (hf : aeval γ f = π ^ N • y) : ∃ h : O[X], aeval γ f = π • aeval γ h := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hy
  set m := Q.natDegree with hm
  set u := π ^ N with hu
  let F : O[X] := ∑ i ∈ Finset.range (m + 1), C (Q.coeff i * u ^ (m - i)) * f ^ i
  have hF : aeval γ F = 0 := by
    have h1 : aeval γ F = u ^ m • aeval y Q := by
      rw [aeval_eq_sum_range (p := Q) y, Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [F, map_sum, map_mul, aeval_C, map_pow, hf]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hAlg : ∀ (c : O) (X : Matrix (Fin n) (Fin n) K), algebraMap O _ c * X = c • X :=
        fun c X => (Algebra.smul_def c X).symm
      have hmi : u ^ (m - i) * u ^ i = u ^ m := by rw [← pow_add, Nat.sub_add_cancel him]
      simp only [_root_.smul_pow, ← map_pow, hAlg, smul_mul_assoc, smul_smul]
      congr 1
      linear_combination (Q.coeff i) * hmi
    rw [h1, show aeval y Q = 0 from hQ, smul_zero]
  have hmon : P₀.Monic := monic_of_injective (IsFractionRing.injective O K) (hγ ▸ γ.charpoly_monic)
  have hd : P₀ ∣ F ^ n := by
    have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ (F.map (algebraMap O K))
      (by rw [aeval_map_algebraMap]; exact hF)
    rw [hγ, Fintype.card_fin, ← Polynomial.map_pow] at h
    exact (map_dvd_map _ (IsFractionRing.injective O K) hmon).1 h
  let φ := residue O
  have hφπ : φ π = 0 := (residue_eq_zero_iff π).2 ((mem_maximalIdeal _).2 hπ.not_isUnit)
  have hFm : F.map φ = (f.map φ) ^ m := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_mul, map_pow]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, hQm.coeff_natDegree, Nat.sub_self,
      pow_zero, mul_one, map_one, C_1, one_mul]
    intro i hi
    have him : 0 < m - i := Nat.sub_pos_of_lt (Finset.mem_range.1 hi)
    rw [hu, map_pow, hφπ, zero_pow (by omega), C_0, zero_pow him.ne', mul_zero, zero_mul]
  have hsep : (P₀.map φ).Separable := by
    unfold Separable
    rw [derivative_map]
    exact hP.map (mapRingHom φ)
  have hd2 : P₀.map φ ∣ (f.map φ) ^ (m * n + 1) := by
    have h := Polynomial.map_dvd φ hd
    rw [Polynomial.map_pow, hFm, ← pow_mul] at h
    exact h.trans (pow_dvd_pow _ (Nat.le_succ _))
  obtain ⟨qb, hqb⟩ := (hsep.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero _)).1 hd2
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective φ (residue_surjective) qb
  have hker : f - P₀ * q ∈ Ideal.span {C π} := by
    have h : f - P₀ * q ∈ RingHom.ker (mapRingHom φ) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
    rwa [Polynomial.ker_mapRingHom, ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      Ideal.map_span, Set.image_singleton] at h
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hker
  refine ⟨h, ?_⟩
  have hP0 : aeval γ P₀ = 0 := by
    rw [← aeval_map_algebraMap K, ← hγ, aeval_self_charpoly]
  have hfe : f = P₀ * q + h * C π := by rw [hh]; ring
  rw [hfe, map_add (f := _), map_mul, map_mul, hP0, zero_mul, zero_add, aeval_C, ← Algebra.commutes,
    ← Algebra.smul_def]

theorem isIntegral_aeval_eq_aeval_map : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  intro O K _ _ _ _ _ _ n P₀ hP γ hγ p hp
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  simp only [aeval_map_algebraMap]
  have hπK : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hπ.ne_zero
  have key : ∀ k : ℕ, ∀ f : O[X], aeval γ f = π ^ k • aeval γ p → ∃ r : O[X], aeval γ p = aeval γ r := by
    intro k
    induction k with
    | zero => intro f hf; exact ⟨f, by rw [hf, pow_zero, one_smul]⟩
    | succ k ih =>
      intro f hf
      obtain ⟨h, hh⟩ := exists_eq_uniformizer_smul P₀ hP γ hγ π hπ _ hp (k + 1) (by omega) f hf
      refine ih h ?_
      have h1 : π • (π ^ k • aeval γ p) = π • aeval γ h := by rw [smul_smul, ← pow_succ', ← hf, hh]
      rw [← algebraMap_smul K π (π ^ k • aeval γ p), ← algebraMap_smul K π (aeval γ h)] at h1
      exact (smul_right_injective _ hπK h1).symm
  obtain ⟨b, hb, hbmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) p
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
  refine key k (C (↑v⁻¹ : O) * IsLocalization.integerNormalization (nonZeroDivisors O) p) ?_
  rw [map_mul, aeval_C, ← aeval_map_algebraMap K γ (IsLocalization.integerNormalization _ p), hbmap,
    ← algebraMap_smul K b p, map_smul, algebraMap_smul, ← Algebra.smul_def, smul_smul, hv,
    ← mul_assoc, Units.inv_mul, one_mul]

end GlobalTheory.MaxOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPart
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.MatrixGaussian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_congr_diagonal (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    ∃ (M : Matrix ι ι ℂ) (d : ι → ℂ), M.det ≠ 0 ∧ (∀ i, 0 < (d i).re) ∧ Mᴴ * A * M = diagonal d := by
  obtain ⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set C := B⁻¹ with hC
  have h1 : B * C = 1 := Matrix.mul_nonsing_inv B hBd
  set A' := Cᴴ * A * C with hA'
  have h2 : A' + A'ᴴ = 1 := by
    have : A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C := by
      simp only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
    rw [this, hBA, star_eq_conjTranspose]
    calc Cᴴ * (Bᴴ * B) * C = (B * C)ᴴ * (B * C) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  have hK : (I • (A' - A'ᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this
  have h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ))) := by
    rw [← h2, smul_smul, I_mul_I]
    module
  refine ⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg det h1
      simp [h] at this
    · intro h
      have := congrArg det hUU
      simp [h] at this
  · calc (C * U)ᴴ * A * (C * U) = Uᴴ * A' * U := by
          simp only [hA', conjTranspose_mul, Matrix.mul_assoc]
      _ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]
      _ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by
          generalize I • (A' - A'ᴴ) = K
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by
          rw [hD, hUU]
          ext i j
          by_cases h : i = j
          · subst h; simp
          · simp [h]

theorem exp_diagonal (d z : ι → ℂ) :
    cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = ∏ i, cexp (-(π * d i) * (‖z i‖ : ℂ) ^ 2) := by
  rw [← Complex.exp_sum, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, ← Complex.conj_mul', Pi.star_apply, RCLike.star_def]
  ring

theorem gaussian_diagonal (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by
  have hb : ∀ i, 0 < ((π : ℂ) * d i).re := fun i => by
    simpa using mul_pos Real.pi_pos (hd i)
  simp only [exp_diagonal]
  constructor
  · refine Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0
  · rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)),
      det_diagonal, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one, div_mul_cancel_left₀ hπ]

theorem map_mulVec_volume (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Measure.map (fun z : ι → ℂ => M *ᵥ z) volume = ENNReal.ofReal (normSq M.det)⁻¹ • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))] at this
  exact this

theorem integral_gaussian (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  obtain ⟨M, d, hM, hd, hMA⟩ := exists_congr_diagonal A hA
  obtain ⟨hi, he⟩ := gaussian_diagonal d hd
  have hn : 0 < normSq M.det := normSq_pos.2 hM
  have hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det := by
    rw [← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  have hd0 : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
    have := hd i
    simp [h] at this
  have hA0 : A.det ≠ 0 := fun h => hd0 (by rw [hdet, h, mul_zero])
  have hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z := fun z => by
    rw [← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) := by fun_prop
  have hcM : Continuous fun z : ι → ℂ => M *ᵥ z := by fun_prop
  have hmap := map_mulVec_volume M hM
  refine ⟨hA0, ?_, ?_⟩
  · have h := (integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2
      (by simpa only [Function.comp_def, hcomp] using hi)
    rw [hmap] at h
    exact (integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h
  · have h := integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable
    simp only [hcomp] at h
    rw [hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul,
      mul_inv, ofReal_inv] at h
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h

end GlobalTheory.MatrixGaussian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpNegHermitianFormPosDef
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.GaussHerm

lemma finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

lemma det_toEuclideanLin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by
  have : Matrix.toEuclideanLin C = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis C := by
    ext v i : 2
    simp [Matrix.toLin_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.single_apply, Pi.single_apply]
  rw [this, LinearMap.det_toLin]

lemma quad_eq {n : ℕ} (H C : Matrix (Fin n) (Fin n) ℂ) (hC : H.transpose = C.conjTranspose * C)
    (w : V n) :
    (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re = ‖Matrix.toEuclideanLin C w‖ ^ 2 := by
  have hH : ∀ j l, H j l = ∑ k, (starRingEnd ℂ) (C k l) * C k j := by
    intro j l
    have := congrFun (congrFun hC l) j
    simpa [Matrix.mul_apply] using this
  have hc : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)) =
      ∑ k, (∑ j, C k j * w j) * (starRingEnd ℂ) (∑ l, C k l * w l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => by ring)))
  rw [hc, EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem exists_eq_conjTranspose_mul_self {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, T = B.conjTranspose * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem integral_exp_neg_herm : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by
  intro n H hH
  have hT : H.transpose.PosDef := Matrix.PosDef.transpose_iff.mpr hH
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hT.posSemidef
  set L : V n →ₗ[ℝ] V n := (Matrix.toEuclideanLin C).restrictScalars ℝ with hL
  have hdetL : LinearMap.det L = Complex.normSq C.det := by
    rw [hL, LinearMap.det_restrictScalars, det_toEuclideanLin, Algebra.norm_complex_apply]
  have hdetC : H.det = (Complex.normSq C.det : ℂ) := by
    rw [← Matrix.det_transpose H, hC, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      mul_comm, Complex.mul_conj]
  have hdetH : H.det.re = Complex.normSq C.det := by rw [hdetC, Complex.ofReal_re]
  have hpos : 0 < Complex.normSq C.det := by
    have := hH.det_pos
    rwa [hdetC, Complex.zero_lt_real] at this
  set g : V n → ℝ := fun v => Real.exp (-1 * ‖v‖ ^ 2) with hg
  have hf : (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) =
      fun w => g (L w) := by
    funext w
    rw [quad_eq H C hC w, hg]
    simp [hL]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (V n)) (f := L)
    (by rw [hdetL]; exact hpos.ne')
  have hG : ∫ v : V n, g v = Real.pi ^ n := by
    rw [hg, GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_V, div_one]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hI : ∫ w : V n, g (L w) = Real.pi ^ n / H.det.re := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hgc.aestronglyMeasurable, hmap, integral_smul_measure, hG, hdetL, hdetH,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hpos), smul_eq_mul,
      div_eq_inv_mul]
  rw [hf]
  refine ⟨Integrable.of_integral_ne_zero ?_, hI⟩
  rw [hI, hdetH]
  exact (div_pos (pow_pos Real.pi_pos n) hpos).ne'

end GlobalTheory.GaussHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

theorem integral_gau_twisted_conv (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add (f := _), inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring

theorem proj_heis_proj {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add (f := _), inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMemFinDimSubspace
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ

end GlobalTheory
end

