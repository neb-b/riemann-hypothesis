module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExp
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson.Dilation

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)

def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_apply_eq_toLp_dil (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE y w = WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)) := by
  ext i
  simp [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, _root_.GlobalTheory.HeckeTheta.dil]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_neg_apply_dilE_apply (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y w) = w := by
  ext i
  simp only [dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, WithLp.ofLp_toLp, Pi.neg_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma det_dilE_eq_exp_sum (y : I → ℝ) : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) = Real.exp (∑ i, y i) := by
  rw [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, LinearMap.det_conj, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, LinearMap.det_pi, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma inner_dilE_dilE_neg (y : I → ℝ) (v l : EuclideanSpace ℂ I) :
    ⟪_root_.GlobalTheory.HeckePoisson.Dilation.dilE y v, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫ = ⟪v, l⟫ := by
  simp [-Complex.ofReal_exp, dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, real_inner_eq_re_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Real.exp (y i / 2) * Real.exp (-y i / 2) = 1 := by
    rw [← Real.exp_add, show y i / 2 + -y i / 2 = 0 by ring, Real.exp_zero]
  linear_combination ((l.ofLp i).re * (v.ofLp i).re + (l.ofLp i).im * (v.ofLp i).im) * h


open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
theorem _root_.GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  let e : EuclideanSpace ℂ I ≃ₗ[ℝ] EuclideanSpace ℂ I :=
    LinearEquiv.ofLinear (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y))
      (LinearMap.ext fun w => by simpa using dilE_neg_apply_dilE_apply (-y) w)
      (LinearMap.ext fun w => dilE_neg_apply_dilE_apply y w)
  have hemb : MeasurableEmbedding (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) ≠ 0 := by
    rw [det_dilE_eq_exp_sum]
    exact (Real.exp_pos _).ne'
  have key := hemb.integral_map (μ := volume)
    (fun u => 𝐞 (-⟪u, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫) • f u)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, integral_smul_measure] at key
  simp only [inner_dilE_dilE_neg] at key
  simp only [dilE_apply_eq_toLp_dil] at key
  rw [Real.fourier_eq, Real.fourier_eq, ← key, det_dilE_eq_exp_sum, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg, Complex.real_smul]

end GlobalTheory.HeckePoisson.Dilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplex
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckeLemma

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_gaussian_two_pi (l : ℂ) :
    𝓕 (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (Real.pi : ℂ))
    (by simp [Real.pi_pos]) l
  have hf : (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
      fun v : ℂ => Complex.exp (-(2 * (Real.pi : ℂ)) * (‖v‖ : ℂ) ^ 2) := by
    funext v; push_cast; ring_nf
  rw [hf, h, Complex.finrank_real_complex]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : ((Real.pi : ℂ) / (2 * Real.pi)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    rw [show (((2 : ℕ) : ℂ) / 2) = 1 by norm_num, Complex.cpow_one]; field_simp
  rw [h1]
  congr 2
  rw [norm_div, Complex.norm_two]
  push_cast
  field_simp

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_exp_neg_pi_norm_sq : Integrable (fun v : ℂ => Real.exp (-Real.pi * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ))
    (by simp [Real.pi_pos]) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_pow_norm_mul_gaussian (m : ℕ) :
    Integrable (fun v : ℂ => ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by
  refine (integrable_exp_neg_pi_norm_sq.const_mul ((m.factorial : ℝ) * Real.exp 1)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
  have hr : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hr m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) ≤
      Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three, sq_nonneg (‖v‖ - 1 / 2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by gcongr
    _ = m.factorial * (Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by ring
    _ ≤ m.factorial * (Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2)) := by gcongr
    _ = _ := by ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem norm_conj_pow_mul_gaussian (n : ℕ) (v : ℂ) :
    ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖ =
      ‖v‖ ^ n * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) :=
  (integrable_pow_norm_mul_gaussian n).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun v => (norm_conj_pow_mul_gaussian n v).le)

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_norm_mul_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ =>
      ‖v‖ * ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖) := by
  refine (integrable_pow_norm_mul_gaussian (n + 1)).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_conj_pow_mul_gaussian]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem hasFDerivAt_conj_pow_mul_gaussian_half (n : ℕ) (l : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ))) L l ∧
      L 1 - Complex.I * L Complex.I = -(2 * Real.pi) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ))) := by
  have hlin : HasFDerivAt (fun z : ℂ => z / 2) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) l := by
    refine (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Complex.real_smul]
    push_cast; ring
  have hP : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (z / 2))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)) l :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp l hlin
  have hN := (hlin.norm_sq).const_mul (-2 * Real.pi)
  have hR : HasFDerivAt (fun z : ℂ => ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) _ l :=
    Complex.ofRealCLM.hasFDerivAt.comp l hN
  have hQ := hR.cexp
  refine ⟨_, ((hP.pow n).mul hQ).const_mul ((1 / 2 : ℂ) * (-Complex.I) ^ n), ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Complex.conjCLE_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul, Function.comp_apply]
  have c2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have e1 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • (1 : ℂ)) = 1 / 2 := by
    simp [Complex.real_smul, c2]
  have e2 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.I) = -Complex.I / 2 := by
    simp [Complex.real_smul, c2]; ring
  have i1 : ⟪l / 2, (1 / 2 : ℝ) • (1 : ℂ)⟫ = l.re / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have i2 : ⟪l / 2, (1 / 2 : ℝ) • Complex.I⟫ = l.im / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have hc : (starRingEnd ℂ) (l / 2) = ((l.re : ℂ) - (l.im : ℂ) * Complex.I) / 2 := by
    apply Complex.ext <;> simp [c2]
  rw [e1, e2, i1, i2, pow_succ]
  simp only [nsmul_eq_mul]
  push_cast
  rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul (g : ℂ → ℂ) (hg : Integrable g)
    (hg' : Integrable (fun v : ℂ => ‖v‖ * ‖g v‖)) (l : ℂ) :
    (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) 1 -
        Complex.I * (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) Complex.I =
      -(2 * Real.pi * Complex.I) * 𝓕 (fun v : ℂ => (starRingEnd ℂ) v * g v) l := by
  have hS : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) g) := by
    refine (hg'.const_mul (2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
      hg.aestronglyMeasurable.fourierSMulRight (Filter.Eventually.of_forall fun v => ?_)
    calc _ ≤ 2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖ * ‖v‖ * ‖g v‖ :=
          VectorFourier.norm_fourierSMulRight_le _ _ _
      _ = _ := by ring
  have hΦ := (Real.fourierIntegral_convergent_iff (μ := volume) l).2 hS
  rw [Real.fourier_eq, Real.fourier_eq, ContinuousLinearMap.integral_apply hΦ,
    ContinuousLinearMap.integral_apply hΦ, ← integral_const_mul,
    ← integral_sub (hΦ.apply_continuousLinearMap 1) ((hΦ.apply_continuousLinearMap Complex.I).const_mul _),
    ← integral_const_mul]
  congr 1
  funext v
  simp only [Circle.smul_def, smul_apply, VectorFourier.fourierSMulRight_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hc : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h1 : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) 1 = v.re := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, (1 : ℂ)⟫ = v.re; simp [Complex.inner])
  have hI : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) Complex.I = v.im := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, Complex.I⟫ = v.im; simp [Complex.inner])
  rw [hc, h1, hI]
  ring_nf
  simp only [Complex.I_sq, Complex.real_smul]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_conj_pow_mul_gaussian (n : ℕ) : ∀ l : ℂ,
    𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  induction n with
  | zero => intro l; simpa using fourier_gaussian_two_pi l
  | succ n ih =>
    intro l
    have hF : 𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
        fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
          ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) :=
      funext ih
    have hd := Real.hasFDerivAt_fourier (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [hF] at hd
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_conj_pow_mul_gaussian_half n l
    have heq := hd.unique hL
    have hA := fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul _ (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [heq, hLv] at hA
    have hfun : (fun v : ℂ => (starRingEnd ℂ) v *
        ((starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ))) =
        fun v : ℂ => (starRingEnd ℂ) v ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      funext v; ring
    rw [hfun] at hA
    have h2pi : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2pi
    rw [← hA]
    linear_combination (-(2 * (Real.pi : ℂ)) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
      ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)))) *
      Complex.I_sq

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_pow_mul_gaussian (m : ℕ) (l : ℂ) :
    𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ m *
        ((l / 2) ^ m * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  have hconj : 𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (starRingEnd ℂ) (𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ m *
        Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) (-l)) := by
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
    congr 1
    funext x
    simp only [Circle.smul_def, inner_neg_right]
    simp only [smul_eq_mul, neg_neg, map_mul, map_pow, Complex.conj_conj,
      ← Complex.exp_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]
  rw [hconj, fourier_conj_pow_mul_gaussian m (-l)]
  simp only [map_mul, map_pow, map_neg, Complex.conj_conj, Complex.conj_I, ← Complex.exp_conj,
    Complex.conj_ofReal, neg_div, norm_neg, map_div₀, map_one, map_ofNat]
  rw [neg_pow (l / 2), neg_pow Complex.I]
  ring


open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
theorem _root_.GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian : ∀ (k : ℤ) (l : ℂ),
    𝓕 (fun w : ℂ => _root_.GlobalTheory.HeckeTheta.hmon k w *
        Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (_root_.GlobalTheory.HeckeTheta.hmon k (l / 2) *
        Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  intro k l
  unfold _root_.GlobalTheory.HeckeTheta.hmon
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = k.toNat by omega]
    exact fourier_conj_pow_mul_gaussian k.toNat l
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = (-k).toNat by omega]
    exact fourier_pow_mul_gaussian (-k).toNat l

end GlobalTheory.HeckeLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLine
section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

open Set

theorem integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent hw
  rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at h
  refine (IntegrableOn.congr_fun (h.const_mul (1 / (c : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le, Complex.ofReal_exp]
  push_cast
  have hne : (c : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hc.ne')
  field_simp

theorem exp_smul_integrand (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem gamma_integral_exp_substitution :
    ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  intro r hr w hw
  set c : ℝ := 2 * Real.pi * r with hcdef
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x)) with hg
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := fun x _ y _ h => Real.exp_injective h
  have hfun : (fun t : ℝ => |Real.exp t| • g (Real.exp t)) =
      fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
    funext t
    exact exp_smul_integrand w c t
  constructor
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj g).mp
      (by rw [himg]; exact integrableOn_cpow_mul_exp_neg_mul hw hc)
    rw [hfun, integrableOn_univ] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [himg, hfun, Measure.restrict_univ] at h2
    rw [← h2, hg, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hc, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, mul_comm]

end GlobalTheory.HeckeMellin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSmoothOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geometricallyConnected_of_smooth_of_section :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  intro k _ X f e _ he _
  exact GlobalTheory.RatPointConn.of_section f e he

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZero
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageInfOfIsSeparatedOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FinNear

theorem isAffineOpen_preimage_inf_of_isSeparated_over {Y X S : Scheme.{0}} (g : Y ⟶ X) (s : X ⟶ S)
    [IsSeparated s] {T : S.Opens} (hT : IsAffineOpen T) {D : X.Opens} (hD : IsAffineOpen D)
    (hDT : D ≤ s ⁻¹ᵁ T) {V : Y.Opens} (hV : IsAffineOpen V) (hVT : V ≤ g ⁻¹ᵁ (s ⁻¹ᵁ T)) :
    IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffine T := hT
  have : IsAffine D := hD
  let g' : V.toScheme ⟶ (s ⁻¹ᵁ T).toScheme := g.resLE (s ⁻¹ᵁ T) V hVT
  have : IsAffineHom (g' ≫ (s ∣_ T)) := isAffineHom_of_isAffine _
  have : IsAffineHom g' := IsAffineHom.of_comp g' (s ∣_ T)
  have hD' : IsAffineOpen ((s ⁻¹ᵁ T).ι ⁻¹ᵁ D) := by
    have h := isAffineOpen_opensRange (X.homOfLE hDT)
    rwa [Scheme.opensRange_homOfLE] at h
  have h := (hD'.preimage g').image_of_isOpenImmersion V.ι
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h

end GlobalTheory.FinNear

namespace GlobalTheory.FinNear

end GlobalTheory.FinNear
end

