module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

theorem inv_inv_real_smul {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s⁻¹ : ℝ) : ℂ) • A)⁻¹ = ((s : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]

theorem inv_real_smul_inv {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s : ℝ) : ℂ) • A)⁻¹ = ((s⁻¹ : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s⁻¹ : ℝ) : ℂ) * ((s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]

theorem scaleFrame_inv {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    (scaleFrame t X v)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹ :=
  inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) (X v) (hX v)

theorem scaleFrame_det_isUnit {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    IsUnit (scaleFrame t X v).det := by
  have hc : (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')
  show IsUnit ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v).det
  rw [Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.mpr hc).pow _).mul (hX v)

theorem dualFrame_scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Formalism.HN.dualFrame (scaleFrame t X) =
      fun v => ((Real.sqrt (t v) : ℝ) : ℂ) • Formalism.HN.dualFrame X v := by
  funext v
  show ((((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)).transpose)⁻¹ =
    ((Real.sqrt (t v) : ℝ) : ℂ) • ((X v).transpose)⁻¹
  rw [Matrix.transpose_smul]
  exact inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) _ (by rw [Matrix.det_transpose]; exact hX v)

theorem sqrt_mul_sqrt_complex (s : ℝ) (hs : 0 < s) : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]

theorem mean_log_sqrt (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))) = meanLog t := by
  unfold meanLog
  have h : ∑ v, Real.log (Real.sqrt (t v)) = (∑ v, Real.log (t v)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => Real.log_sqrt (ht v).le
  rw [h]
  ring

theorem mean_log_sqrt_inv (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))⁻¹) = -meanLog t := by
  unfold meanLog
  have h : ∑ v, Real.log (Real.sqrt (t v))⁻¹ = -((∑ v, Real.log (t v)) / 2) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [Real.log_inv, Real.log_sqrt (ht v).le]
  rw [h]
  ring

theorem gram_scaleFrame [StarRing K] {d m : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (e : Fin m → Fin d → K) :
    gram (scaleFrame t X) v e = (t v : ℂ) • gram X v e := by
  have hs := scaleFrame_inv t ht X hX v
  have hmv : ∀ (u : Fin d → ℂ) (i : Fin d), ((((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹) *ᵥ u) i =
      ((Real.sqrt (t v) : ℝ) : ℂ) * (((X v)⁻¹) *ᵥ u) i := by
    intro u i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  ext a c
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, hs, hmv, star_mul', map_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sqrt_mul_sqrt_complex (t v) (ht v)]
  ring

theorem meanLog_mul (t κ : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (hκ : ∀ v, 0 < κ v) :
    meanLog (fun v => t v * κ v) = meanLog t + meanLog κ := by
  unfold meanLog
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => Real.log_mul (ht v).ne' (hκ v).ne'

theorem opNormAt_scale_alt [StarRing K] {n D : ℕ} (s : ℝ) (hs : 0 < s)
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y Y' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hY : IsUnit (Y v).det) (hY' : Y' v = ((s : ℝ) : ℂ) • Y v)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y' v φ =
      s⁻¹ * Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by
  unfold Formalism.HN.opNormAt
  rw [hY', inv_real_smul_inv s hs (Y v) hY, Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul,
    norm_smul, Complex.norm_of_nonneg (inv_nonneg.mpr hs.le)]

theorem opNormAt_pos_alt [StarRing K] {n D : ℕ}
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hXN : IsUnit (XN v).det) (hY : IsUnit (Y v).det)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) (hφ : φ ≠ 0) :
    0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by
  unfold Formalism.HN.opNormAt
  rw [norm_pos_iff]
  intro h0
  apply hφ
  have hA : (Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding * XN v = 0 :=
    (Matrix.toEuclideanLin).map_eq_zero_iff.mp (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0)
  have hM : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding = 0 := by
    have e1 : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
        φ).map v.embedding = Y v * ((Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n))
        (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding * XN v) * (XN v)⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXN, Matrix.mul_one]
    rw [e1, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ = 0 := by
    ext i j
    have h1 := congrArg (fun A => A i j) hM
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1
    exact (map_eq_zero_iff _ v.embedding.injective).mp h1
  exact (LinearMap.toMatrix _ _).map_eq_zero_iff.mp hT

end SlopeTestRemainingChoices

theorem lattice_fg_ne_bot {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {D : ℕ}
    (hD : 0 < D) (R : Submodule (𝓞 K) (Fin D → K)) (hR : Submodule.IsFullLattice K R) :
    R.FG ∧ R ≠ ⊥ := by
  refine ⟨hR.toIsLattice.fg, ?_⟩
  rintro rfl
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have h := hR.span_eq_top
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
  exact bot_ne_top h

theorem kappa_invariance : KappaInvariance := by
  intro K _ _ _ _ D hD XE hXE t ht
  have hsq : ∀ v, 0 < Real.sqrt (t v) := fun v => Real.sqrt_pos.mpr (ht v)
  have hXd : ∀ v, IsUnit (Formalism.HN.dualFrame XE v).det := by
    intro v
    simp only [Formalism.HN.dualFrame]
    rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
    exact hXE v

  have hdual : ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                (Formalism.HN.dualLat R) =
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
          meanLog t := by
    intro R hR
    have hfg : R.FG := hR.toIsLattice.fg
    have hspan : Submodule.span K (R : Set (Fin D → K)) = ⊤ := hR.span_eq_top
    obtain ⟨hdfg, hdspan, -⟩ :=
      Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R hfg hspan
    have hne : Formalism.HN.dualLat R ≠ ⊥ := by
      intro h
      rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hdspan
      let b := (Pi.basisFun K (Fin D)).dualBasis
      have hb : b ⟨0, hD⟩ ∈ (⊤ : Submodule K _) := Submodule.mem_top
      rw [← hdspan, Submodule.mem_bot] at hb
      exact b.ne_zero _ hb
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Module.Dual K (Fin D → K)) (Fin D)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (fun v => Real.sqrt (t v)) hXd hsq
      (Formalism.HN.dualLat R) hdfg
    have h1 := (h hne).1
    rw [dualFrame_scaleFrame t ht XE hXE, h1, mean_log_sqrt t ht]
  refine ⟨fun v => ⟨scaleFrame_det_isUnit t ht XE hXE v, ?_⟩, ?_, fun κ hκ => meanLog_mul t κ ht hκ, ?_, ?_⟩
  · rw [scaleFrame_inv t ht XE hXE v, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_ofReal, sqrt_mul_sqrt_complex _ (ht v)]
  · intro d XS φ v
    simp only [detRatio, gram_scaleFrame t ht XE hXE v, Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_div_assoc]
  · intro R hR
    obtain ⟨hfg, hne⟩ := lattice_fg_ne_bot hD R hR
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Fin D → K) (Fin D)
      (Pi.basisFun K (Fin D)) XE (fun v => (Real.sqrt (t v))⁻¹) hXE (fun v => inv_pos.mpr (hsq v))
      R hfg
    obtain ⟨h1, h2, -⟩ := h hne
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    refine ⟨?_, hdual R hR, ?_, ?_⟩
    · have e1 := dual_lattice_measure K D hD XE hXE R hR
      have e2 := dual_lattice_measure K D hD (scaleFrame t XE) (scaleFrame_det_isUnit t ht XE hXE) R hR
      rw [hdual R hR, e1] at e2
      field_simp at e2
      linarith
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h1, mean_log_sqrt_inv t ht]; ring
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h2, mean_log_sqrt_inv t ht]; ring
  · intro n XN hXN φ hφ
    have hop : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE)) v φ ^ 2) =
        Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v φ ^ 2) - Real.log (t v) := by
      intro v
      have hp := opNormAt_pos_alt XN (Formalism.HN.dualFrame XE) v (hXN v) (hXd v) φ hφ
      rw [opNormAt_scale_alt (Real.sqrt (t v)) (hsq v) XN (Formalism.HN.dualFrame XE) _ v (hXd v)
        (by rw [dualFrame_scaleFrame t ht XE hXE]) φ, mul_pow, inv_pow, Real.sq_sqrt (ht v).le,
        Real.log_mul (inv_pos.mpr (ht v)).ne' (pow_pos hp 2).ne', Real.log_inv]
      ring
    simp only [Formalism.HN.htMap, hop, Finset.sum_sub_distrib, meanLog]
    ring

theorem meanLog_inv {K : Type} [Field K] [NumberField K] (κ : InfinitePlace K → ℝ) :
    meanLog (fun v => (κ v)⁻¹) = -meanLog κ := by
  unfold meanLog
  simp only [Real.log_inv, Finset.sum_neg_distrib, mul_neg]

theorem kappa_normalise : KappaNormalise := by
  intro K _ _ _ _ D hD XE hXE κ hκ
  obtain ⟨h1, h2, -, h4, h5⟩ := kappa_invariance K D hD XE hXE (fun v => (κ v)⁻¹)
    (fun v => inv_pos.mpr (hκ v))
  rw [meanLog_inv] at h4 h5
  refine ⟨fun v => (h1 v).1, ?_, ?_, by simp [meanLog], ?_⟩
  · intro XS φ v ρ P h
    rw [h2 D XS φ v, h, mul_pow, mul_pow, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro XS φ v P h
    rw [h2 D XS φ v, h, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro R hR
    obtain ⟨-, e2, -, e4⟩ := h4 R hR
    refine ⟨by rw [e2]; ring, by rw [e4]; ring, by rw [e2, e4]; ring, ?_⟩
    intro n XN hXN φ hφ
    have e5 := h5 n XN hXN φ hφ
    exact ⟨by rw [e5]; ring, by rw [e2, e5]; ring⟩

end Formalism.DivisionValues
