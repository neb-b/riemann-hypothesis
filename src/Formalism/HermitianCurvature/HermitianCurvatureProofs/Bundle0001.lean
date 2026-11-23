module

public import Mathlib
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CoeffOfValues
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

section vand

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def vN (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde fun m : Fin (d + 1) => ((m : ℕ) : ℂ)

theorem vN_det (d : ℕ) : IsUnit (vN d).det := by
  rw [isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := h
  exact Fin.ext (by exact_mod_cast h')

theorem coeff_of_values (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by
  have hinv : (vN d)⁻¹ * vN d = 1 := Matrix.nonsing_inv_mul _ (vN_det d)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' =
      ((vN d)⁻¹ * vN d) n n' • c n' := by
    intro n'
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
  simp_rw [e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end vand

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem poly_integral (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set W := (vN d)⁻¹ with hW

  set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hI _).smul (W n m)
  have hCeq : ∀ n, ∫ x, C n x ∂μ = ∑ m, W n m • ∫ x, I ((m : ℕ) : ℝ) x ∂μ := by
    intro n
    show ∫ x, ∑ m, W n m • I ((m : ℕ) : ℝ) x ∂μ = _
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun m x => W n m • I ((m : ℕ) : ℝ) x)
      (fun m _ => (hI _).smul (W n m))
    rw [this]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_smul]

  have hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x := by
    filter_upwards [hP] with x ⟨c, hc, hcx⟩
    have hCc : ∀ n, C n x = c n := by
      intro n
      rw [hC]
      simp only
      simp_rw [hcx]
      have := coeff_of_values d c n
      simpa [hW] using this
    refine ⟨fun y => ?_, by rw [hCc, hc]⟩
    rw [hcx y]
    simp_rw [hCc]
  refine ⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩
  · exact integral_congr_ae (hae.mono fun x hx => hx.2)
  · rw [integral_congr_ae (hae.mono fun x hx => hx.1 y)]
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x)
      (fun n _ => (hCint n).smul _)
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_smul]

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtTMul
section
open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz
section
namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralIteratedFDerivEqZero
section
open MeasureTheory Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem integral_fderiv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : V → W} (hd : Differentiable ℝ F) (hF : Integrable F) (hF' : Integrable (fderiv ℝ F)) (v : V) :
    ∫ x, fderiv ℝ F x v = 0 := by
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : V => (1 : ℝ)) (f' := fun _ => 0) (g := F) (g' := fderiv ℝ F) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (by simp) (by simpa using hF'.apply_continuousLinearMap v) (by simpa using hF)
    (fun x _ => hasFDerivAt_const _ _) (fun x _ => hd x |>.hasFDerivAt)
  simpa using h

theorem integrable_of_decay {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u :=
  ((integrable_one_add_norm (by linarith)).const_mul C).mono' hu.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hdec x)

theorem integral_iteratedFDeriv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {D : V → W} {m : ℕ} (hD : ContDiff ℝ m D) (C : ℝ)
    (hdec : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  have hint : ∀ i ≤ m, Integrable (iteratedFDeriv ℝ i D) := fun i hi =>
    integrable_of_decay (hD.continuous_iteratedFDeriv (by exact_mod_cast hi)) C (hdec i hi)
  refine ⟨hint j hjm, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i D) :=
    hD.differentiable_iteratedFDeriv (by exact_mod_cast (show i < m by omega))
  have hF' : Integrable (fderiv ℝ (iteratedFDeriv ℝ i D)) := by
    have h := hint (i + 1) hjm
    have hc1 : ContDiff ℝ 1 (iteratedFDeriv ℝ i D) :=
      hD.iteratedFDeriv_right (by exact_mod_cast (show 1 + i ≤ m by omega))
    refine h.norm.mono' (hc1.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_fderiv_iteratedFDeriv]
  ext m'
  rw [ContinuousMultilinearMap.integral_apply (hint (i + 1) hjm)]
  simp only [iteratedFDeriv_succ_apply_left, ContinuousMultilinearMap.zero_apply]
  have h0 := integral_fderiv_eq_zero hdiff (hint i (by omega)) hF' (m' 0)
  rw [← ContinuousMultilinearMap.integral_apply (hF'.apply_continuousLinearMap (m' 0)), h0]
  rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MomentIntegrable
section
open MeasureTheory Real Module
open scoped FourierTransform

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem moment_integrable {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have h0 : (0 : ℝ) < 1 + ‖v‖ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ n * ‖u v‖ ≤ (1 + ‖v‖) ^ n * (C * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        gcongr
        · linarith [norm_nonneg v]
        · exact hdec v
    _ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        rw [Real.rpow_natCast]; ring
    _ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by
        rw [← Real.rpow_add h0]
    _ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by
        gcongr
        have : (n : ℝ) ≤ m := by exact_mod_cast hn
        linarith

theorem fourier_smooth (D : V → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ w, ‖𝓕 D w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) :
    ∃ D' : V → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  set g : V → ℂ := 𝓕 D with hg
  have hgc : Continuous g :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hD
  set h : V → ℂ := fun x => g (-x) with hh
  have hhc : Continuous h := hgc.comp continuous_neg
  have hhd : ∀ w, ‖h w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by
    intro w
    have := hdec (-w)
    rwa [norm_neg] at this
  have hmom : ∀ n : ℕ, n ≤ m → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    moment_integrable hhc m C hhd
  have hmomN : ∀ n : ℕ, (n : ℕ∞) ≤ (m : ℕ∞) → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    fun n hn => hmom n (by exact_mod_cast hn)
  have hgi : Integrable g := by
    have := moment_integrable hgc m C hdec 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hgc.aestronglyMeasurable).1 this
  have hinv : 𝓕 h = 𝓕⁻ g := (fourierInv_eq_fourier_comp_neg g).symm
  refine ⟨𝓕 h, Real.contDiff_fourier hmomN, fun j hj => ?_, fun t ht => ?_⟩
  · refine ⟨∫ v, (2 * π * ‖innerSL ℝ (E := V)‖) ^ j * (‖v‖ ^ j * ‖h v‖), fun t => ?_⟩
    rw [Real.iteratedFDeriv_fourier hmomN hhc.aestronglyMeasurable (by exact_mod_cast hj)]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
      ((hmom j hj).const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) h v j
    simpa [mul_assoc] using this
  · rw [hinv]
    exact hD.fourierInv_fourier_eq hgi ht

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Finset
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section hilbert

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_sum_smul (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_right, hv]
  ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem form_sum_conj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
  ring

theorem norm_sq_sum_eq_form (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_smul k v hv, form_sum_conj, RCLike.re_to_complex]
  congr 1
  refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
  rw [hy j hj l hl]

theorem norm_sum_le_of_form {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by
  have h := norm_sq_sum_eq_form k v hv B J a P y hy
  have h2 := hB (∑ j ∈ J, conj (a j) • y j)
  rw [← h] at h2
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h3 => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end hilbert

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfGram
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Finset
open scoped ComplexConjugate InnerProductSpace

theorem norm_sq_comb {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by
  rw [show ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ⟪∑ j ∈ J, b j • y j, ∑ j ∈ J, b j • y j⟫_ℂ by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem sum_sq_le_sq_sum {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)

theorem norm_sum_le_of_gram {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by
  have h1 : ((‖∑ j ∈ J, a j • v (P j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_comb]
    calc ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * ⟪v (P j), v (P l)⟫_ℂ
        = ∑ j ∈ J, ∑ l ∈ J, ∑ i, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
          rw [← hv, hk j hj l hl, mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j ∈ J, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          exact (sum_congr rfl fun j _ => sum_comm).trans sum_comm
      _ = ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
          refine sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_mul, norm_sq_comb, mul_sum, sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [Complex.conj_conj]
          ring
  have h2 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 ≤ (∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
    rw [h2]
    have : ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 =
        ∑ i, (√(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc i)]
    rw [this]
    exact sum_sq_le_sq_sum _ fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ :=
    sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ j ∈ J, a j • v (P j))]

end Formalism.FourierDecayAlt.P.GermRateSplit
end

