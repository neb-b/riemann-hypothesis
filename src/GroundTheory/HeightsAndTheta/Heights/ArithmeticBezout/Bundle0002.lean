module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramHess
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem ChartGram.hasFDerivAt_re_inner {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y :=
  Complex.reCLM.hasFDerivAt.comp y (HasFDerivAt.inner ℂ hu hw)

theorem ChartGram.re_inner_self_pos {x : F} (h0 : x ≠ 0) : 0 < (⟪x, x⟫_ℂ).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have h' : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := h
  rw [h']; positivity

theorem ChartGram.re_inner_comm (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by
  rw [← inner_conj_symm x z, Complex.conj_re]

theorem ChartGram.fderiv_half_log_apply {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by
  have h1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y := hu.hasFDerivAt.restrictScalars ℝ
  have h4 := HasFDerivAt.const_mul (HasFDerivAt.log (ChartGram.hasFDerivAt_re_inner h1 h1)
    (ChartGram.re_inner_self_pos h0).ne') 2⁻¹
  rw [h4.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, Complex.add_re, smul_eq_mul]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y b)]
  ring

theorem ChartGram.hessian_half_log_apply [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by
  set ψ : E → ℝ := fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re with hψ
  have hy : AnalyticAt ℂ u y := hu.self_of_nhds
  have hN := ChartGram.re_inner_self_pos h0

  have hc : ContDiffAt ℝ 2 ψ y := by
    have hu2 : ContDiffAt ℝ 2 u y := (hy.contDiffAt (n := 2)).restrict_scalars ℝ
    have hi : ContDiffAt ℝ 2 (fun y' => (⟪u y', u y'⟫_ℂ).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (ContDiffAt.inner ℂ hu2 hu2)
    exact contDiffAt_const.mul (hi.log hN.ne')
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fun y' => fderiv ℝ ψ y' b) y a := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [h2]

  have hev : (fun y' => fderiv ℝ ψ y' b) =ᶠ[𝓝 y]
      fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹ := by
    filter_upwards [hu, hy.continuousAt.eventually_ne h0] with y' h1 h2
    exact ChartGram.fderiv_half_log_apply h1.differentiableAt h2 b
  rw [hev.fderiv_eq]
  have hu1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y :=
    hy.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hW : HasFDerivAt (fun y' => fderiv ℂ u y' b)
      (((fderiv ℂ u y).comp (0 : E →L[ℂ] E) + (fderiv ℂ (fderiv ℂ u) y).flip b).restrictScalars ℝ) y :=
    (hy.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).restrictScalars ℝ
  have hI := (hasDerivAt_inv hN.ne').comp_hasFDerivAt y (ChartGram.hasFDerivAt_re_inner hu1 hu1)
  have hg := HasFDerivAt.mul (ChartGram.hasFDerivAt_re_inner hu1 hW) hI
  have hg' : HasFDerivAt (fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹) _ y := hg
  rw [hg'.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.add_re, smul_eq_mul,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    zero_add, Function.comp_apply]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y a) (u y)]
  ring


open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian) in
theorem ChartGram.cxHessian_half_log [CompleteSpace F] {D : ℕ} {u : (Fin D → ℂ) → F}
    {y : Fin D → ℂ} (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (i j : Fin D) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y i j =
      (⟪u y, u y⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), fderiv ℂ u y (Pi.single i 1)⟫_ℂ -
          ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), u y⟫_ℂ) /
        (2 * ⟪u y, u y⟫_ℂ ^ 2) := by
  have hN := ChartGram.re_inner_self_pos h0
  have hNc : ⟪u y, u y⟫_ℂ = ((⟪u y, u y⟫_ℂ).re : ℂ) := by
    rw [← inner_self_ofReal_re (𝕜 := ℂ)]; rfl
  unfold cxHessian
  simp only [ChartGram.hessian_half_log_apply hu h0, map_smul, smul_apply,
    inner_smul_right, inner_smul_left, Complex.conj_I]
  rw [← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (u y),
    ← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (fderiv ℂ u y (Pi.single i 1)), hNc]
  generalize ⟪u y, fderiv ℂ (fderiv ℂ u) y (Pi.single i 1) (Pi.single j 1)⟫_ℂ = Q
  generalize ⟪fderiv ℂ u y (Pi.single i 1), fderiv ℂ u y (Pi.single j 1)⟫_ℂ = P
  generalize ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ = p
  generalize ⟪u y, fderiv ℂ u y (Pi.single j 1)⟫_ℂ = q
  generalize (⟪u y, u y⟫_ℂ).re = N at hN ⊢
  have hN' : N ≠ 0 := hN.ne'
  apply Complex.ext <;>
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramPolar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem ChartGram.sum_neg_one_pow_card_pow (D : ℕ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℂ)) (fun r : ℂ => r ^ D) D 0
  rw [fwdDiff_iter_eq_factorial] at h1
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := fun m => (-1 : ℂ) ^ (D - m) * (m : ℂ) ^ D)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h2 : ((D.factorial : ℂ → ℂ) 0) = (D.factorial : ℂ) := rfl
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

theorem ChartGram.mixedDisc_const {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  unfold mixedDisc
  have h : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h, ← Finset.sum_mul, ChartGram.sum_neg_one_pow_card_pow]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeAvoid.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → K) (σ : K →+* ℂ), IsProjPrime I → linForm u ∉ I →
      ∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, linForm (fun j => σ (u j)) ∉ W

def coneBall {n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0}

def ConeBallFinite.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤

def ConeFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      IntegrableOn (fun y => fsLog h u (h.pointOf y)) (coneBall h W)
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

def ConeHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjPrimeHasPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)), IsProjPrime W →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ q ∈ W, aeval x q = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem map_eq_maximalIdeal_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W J hW,
    ← IsLocalization.map_radical W.primeCompl (Localization.AtPrime W) J, hJ.radical]

theorem localMult_eq_one_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by
  have hWp : W.IsPrime := hW.1.1
  unfold localMult
  rw [dite_eq_left hWp, map_eq_maximalIdeal_of_isRadical hJ hW]
  have : IsSimpleModule (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one]
  rfl

theorem fundCycle_apply_of_isRadical {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by
  classical
  have hval : fundCycle J W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  unfold fundCycle
  rw [Finsupp.onFinset_apply, if_pos hrel]
  exact localMult_eq_one_of_isRadical hJ hrel.1

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace KernelProjMeasurable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

def shifted (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ContinuousLinearMap.adjoint A) ∘L A + (ε : ℂ) • (1 : E →L[ℂ] E)

theorem re_inner_shifted (A : E →L[ℂ] F) (ε : ℝ) (u : E) :
    RCLike.re (inner ℂ u (shifted A ε u)) = ‖A u‖ ^ 2 + ε * ‖u‖ ^ 2 := by
  simp only [shifted, add_apply, comp_apply, smul_apply, one_apply, inner_add_right,
    inner_smul_right, adjoint_inner_right, inner_self_eq_norm_sq_to_K, map_add]
  simp [← Complex.ofReal_pow]

theorem inner_shifted_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by
  simp [shifted, inner_add_right, inner_smul_right, adjoint_inner_right, hz]

theorem shifted_apply_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by
  simp [shifted, hz]

theorem mul_norm_le_norm_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) (u : E) :
    ε * ‖u‖ ≤ ‖shifted A ε u‖ := by
  have h1 := re_inner_shifted A ε u
  have h2 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · have h3 : (ε * ‖u‖) * ‖u‖ ≤ ‖shifted A ε u‖ * ‖u‖ := by
      nlinarith [sq_nonneg ‖A u‖]
    exact le_of_mul_le_mul_right h3 h

theorem isUnit_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) : IsUnit (shifted A ε) := by
  have hinj : Function.Injective (shifted A ε : E →ₗ[ℂ] E) := by
    intro a b hab
    have h := mul_norm_le_norm_shifted A hε (a - b)
    have hab' : shifted A ε a = shifted A ε b := hab
    rw [map_sub, hab', sub_self, norm_zero] at h
    have h0 : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv.toUnit, ?_⟩
  ext v
  rfl

theorem exists_norm_le_norm_shifted (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  have hinj : Function.Injective ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (u : E) ∈ K := hu
    have h2 : (u : E) ∈ K ⊓ Kᗮ := ⟨h1, u.2⟩
    rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨c, -, hc⟩ := ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype).injective_iff_antilipschitz.1 hinj
  refine ⟨(c : ℝ) ^ 2, sq_nonneg _, fun ε hε u hu => ?_⟩
  have h1 : ‖u‖ ≤ c * ‖A u‖ := by
    simpa using hc.le_mul_norm (map_zero _) ⟨u, hu⟩
  have h2 := re_inner_shifted A ε u
  have h3 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  have hc0 : (0 : ℝ) ≤ c := c.2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have hAu : ‖u‖ ^ 2 ≤ (c : ℝ) ^ 2 * ‖A u‖ ^ 2 := by
      have := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      nlinarith
    have h4 : (c : ℝ) ^ 2 * ‖A u‖ ^ 2 ≤ (c : ℝ) ^ 2 * (‖u‖ * ‖shifted A ε u‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [mul_nonneg hε (sq_nonneg ‖u‖)]
    have h5 : ‖u‖ * ‖u‖ ≤ ((c : ℝ) ^ 2 * ‖shifted A ε u‖) * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 h

def resolvent (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ε : ℂ) • Ring.inverse (shifted A ε)

theorem exists_norm_resolvent_sub_le (A : E →L[ℂ] F) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_norm_shifted A
  refine ⟨2 * C, fun ε hε => ?_⟩
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := (resolvent A ε - K.starProjection) v with hu_def
  have hinv : shifted A ε (Ring.inverse (shifted A ε) v) = v := by
    have := Ring.mul_inverse_cancel _ (isUnit_shifted A hε)
    exact congrArg (fun T : E →L[ℂ] E => T v) this
  have hPv : A (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hTu : shifted A ε u = (ε : ℂ) • (v - K.starProjection v) := by
    rw [hu_def, resolvent, sub_apply, smul_apply, map_sub, map_smul, hinv,
      shifted_apply_of_apply_eq_zero A ε hPv, smul_sub]
  have hu : u ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 := inner_shifted_of_apply_eq_zero A ε u hz
    rw [hTu, inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 (K.sub_starProjection_mem_orthogonal v) z hz, mul_zero] at h1
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hε'
  have hvP : ‖v - K.starProjection v‖ ≤ 2 * ‖v‖ :=
    (norm_sub_le _ _).trans (by linarith [K.norm_starProjection_apply_le v])
  calc ‖u‖ ≤ C * ‖shifted A ε u‖ := hCb ε hε.le u hu
    _ = C * (ε * ‖v - K.starProjection v‖) := by
      rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ C * (ε * (2 * ‖v‖)) := by gcongr
    _ = 2 * C * ε * ‖v‖ := by ring

theorem tendsto_resolvent (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by
  obtain ⟨C, hC⟩ := exists_norm_resolvent_sub_le A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hC _ (by positivity)) ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

theorem continuous_resolvent {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by
  have hadj : Continuous fun x => ContinuousLinearMap.adjoint (A x) :=
    ContinuousLinearMap.adjoint.continuous.comp hA
  have hT : Continuous fun x => shifted (A x) ε := by
    simp only [shifted]
    exact (hadj.clm_comp hA).add continuous_const
  have hI : Continuous fun x => Ring.inverse (shifted (A x) ε) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h := NormedRing.inverse_continuousAt (isUnit_shifted (A x) hε).unit
    rw [IsUnit.unit_spec] at h
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun x => shifted (A x) ε) h hT.continuousAt
  show Continuous fun x => (ε : ℂ) • Ring.inverse (shifted (A x) ε)
  exact hI.const_smul (ε : ℂ)

end KernelProjMeasurable

theorem KernelProjMeasurable.proof : KernelProjMeasurable.Statement := by
  intro X _ _ _ n k L hL
  let A : X → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
    fun x => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L x))
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro v
    change Continuous fun x => (WithLp.toLp 2 (Matrix.mulVec (L x) (WithLp.ofLp v)) : EuclideanSpace ℂ (Fin k))
    exact (PiLp.continuous_toLp 2 _).comp (hL.matrix_mulVec continuous_const)
  refine measurable_of_tendsto_metrizable
    (f := fun j x => KernelProjMeasurable.resolvent (A x) (1 / ((j : ℝ) + 1)))
    (fun j => (KernelProjMeasurable.continuous_resolvent hA (by positivity)).measurable) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact KernelProjMeasurable.tendsto_resolvent (A x)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFundCycleBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))

end GroundTheory.Heights₂.Heights
end

