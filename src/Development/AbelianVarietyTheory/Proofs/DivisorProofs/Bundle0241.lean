module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigma
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoAB

open MeasureTheory GlobalTheory.HeckeTwoC

def wt (y t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I

def L (y t : ℝ) : ℝ := Real.log |y| + lg (t / y)

theorem wt_eq {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t = (y : ℂ) * (((t / y : ℝ) : ℂ) + I) := by
  unfold wt
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  push_cast
  field_simp

theorem norm_wt {y : ℝ} (hy : y ≠ 0) (t : ℝ) : ‖wt y t‖ = Real.exp (L y t) := by
  rw [wt_eq hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, L, Real.exp_add,
    Real.exp_log (abs_pos.2 hy), ← norm_tI_eq]

theorem wt_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp [wt] at this; exact hy this

def F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b * Complex.exp ((L y t : ℂ) * (-2 * σ)) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def F' (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b *
    (Complex.exp ((L y t : ℂ) * (-2 * σ)) * ((L y t : ℂ) * (-2))) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_eq (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (fun σ => hTransAB a b σ ν y) = fun σ => ∫ t, F a b ν y σ t := by
  funext σ
  unfold hTransAB F
  congr 1; funext t
  congr 2
  rw [show (t : ℂ) + (y : ℂ) * I = wt y t from rfl, norm_wt hy,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]

theorem norm_e (ν t : ℝ) : ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem norm_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) := by
  unfold F
  rw [norm_mul, norm_mul, norm_mul, norm_e, norm_pow, norm_pow, norm_inv, norm_inv, Complex.norm_conj,
    norm_wt hy, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F' a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|) := by
  have : F' a b ν y σ t = F a b ν y σ t * ((L y t : ℂ) * (-2)) := by unfold F F'; ring
  rw [this, norm_mul, norm_F a b ν hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp; ring

theorem bound_exp {ε M c L0 D : ℝ} (hc : 1 + 2 * ε ≤ c) (hM : c ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.exp (-c * (L0 + D)) ≤ Real.exp (M * |L0|) * Real.exp (-(1 + ε) * D) * Real.exp (-(ε * D)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := le_abs_self L0
  have h2 := neg_abs_le L0
  have h3 := abs_nonneg L0
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : 0 ≤ |L0| + L0),
    mul_nonneg (by linarith : 0 ≤ M - c) h3, mul_nonneg (by linarith : 0 ≤ c - 1 - 2 * ε) hD]

theorem bound_F {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F a b ν y σ t‖ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F a b ν hy]
  have hD := lg_nonneg (t / y)
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have h2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) := h
    _ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _

theorem bound_F' {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F' a b ν y σ t‖ ≤
      2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F' a b ν hy]
  have hD : 0 ≤ lg (t / y) := lg_nonneg _
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have hL : |L y t| ≤ |Real.log (abs y)| + lg (t / y) := by
    unfold L; exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hD])
  have hE2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE2D : Real.exp (-(ε * lg (t / y))) * lg (t / y) ≤ 1 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg (t / y))
    have := Real.add_one_le_exp (ε * lg (t / y))
    rw [show (Real.exp (ε * lg (t / y)))⁻¹ * lg (t / y) * ε = (ε * lg (t / y)) / Real.exp (ε * lg (t / y)) by
      field_simp]
    rw [div_le_iff₀ hp]; linarith
  have heC : 0 ≤ Real.exp (M * |Real.log (abs y)|) := (Real.exp_pos _).le
  have hE1 : 0 ≤ Real.exp (-(1 + ε) * lg (t / y)) := (Real.exp_pos _).le
  have hE2p : 0 ≤ Real.exp (-(ε * lg (t / y))) := (Real.exp_pos _).le
  have hl0 := abs_nonneg (Real.log |y|)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) *
          (2 * (|Real.log (abs y)| + lg (t / y))) :=
        mul_le_mul h (by linarith) (by positivity) (by positivity)
    _ = 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) *
          (Real.exp (-(ε * lg (t / y))) * |Real.log (abs y)| + Real.exp (-(ε * lg (t / y))) * lg (t / y)) := by ring
    _ ≤ 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * (1 * |Real.log (abs y)| + 1 / ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hE2 hl0) hE2D) (by positivity)
    _ = _ := by ring

theorem integrable_bound {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : y ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg (t / y))) :=
  (integrable_expL hε).comp_div hy

theorem hasDerivAt_F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) :
    HasDerivAt (fun s => F a b ν y s t) (F' a b ν y σ t) σ := by
  unfold F F'
  have h : HasDerivAt (fun s : ℂ => (L y t : ℂ) * (-2 * s)) ((L y t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (L y t : ℂ)).congr_deriv (by ring)
  exact (h.cexp.const_mul _).mul_const _

theorem continuous_L {y : ℝ} : Continuous (L y) := by
  unfold L
  exact continuous_const.add (continuous_lg.comp (continuous_id.div_const y))

theorem continuous_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F a b ν y σ) := by
  unfold F
  have hw : Continuous (wt y) := by unfold wt; fun_prop
  have h1 : Continuous fun t => (wt y t)⁻¹ := hw.inv₀ (wt_ne hy)
  have h2 : Continuous fun t => ((starRingEnd ℂ) (wt y t))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => (map_ne_zero _).2 (wt_ne hy t))
  have h3 : Continuous fun t => Complex.exp ((L y t : ℂ) * (-2 * σ)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)
  have h4 : Continuous fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by fun_prop
  exact (((h1.pow a).mul (h2.pow b)).mul h3).mul h4

theorem continuous_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F' a b ν y σ) := by
  have : F' a b ν y σ = fun t => F a b ν y σ t * ((L y t : ℂ) * (-2)) := by funext t; unfold F F'; ring
  rw [this]
  exact (continuous_F a b ν hy σ).mul ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)

end GlobalTheory.HeckeTwoAB

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB

theorem hTransAB_differentiableOn : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 →
    DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  intro a b ν y hab hy
  rw [hTransAB_eq a b ν hy]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hab' : (2 : ℝ) ≤ (a + b : ℝ) := by exact_mod_cast hab
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re ∧ σ.re ≤ σ₀.re + ε := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := abs_lt.1 (lt_of_le_of_lt h1 h2)
    simp only [sub_re] at h3
    constructor <;> linarith [h3.1, h3.2]
  set M := (a + b : ℝ) + 2 * (σ₀.re + ε) with hM_def
  have hc : ∀ σ ∈ Metric.ball σ₀ ε, 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re := by
    intro σ hσ; have := (hball σ hσ).1; linarith
  have hM : ∀ σ ∈ Metric.ball σ₀ ε, (a + b : ℝ) + 2 * σ.re ≤ M := by
    intro σ hσ; have := (hball σ hσ).2; rw [hM_def]; linarith
  have h0 := Metric.mem_ball_self hε (x := σ₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F a b ν y)
    (F' := F' a b ν y) (x₀ := σ₀)
    (bound := fun t => 2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) *
      Real.exp (-(1 + ε) * lg (t / y)))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_F a b ν hy σ).aestronglyMeasurable)
    (((integrable_bound hε hy).const_mul (Real.exp (M * |Real.log (abs y)|))).mono'
      (continuous_F a b ν hy σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_F hε a b ν hy (hc σ₀ h0) (hM σ₀ h0) t))
    (continuous_F' a b ν hy σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_F' hε a b ν hy (hc σ hσ) (hM σ hσ) t)
    ((integrable_bound hε hy).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_F a b ν y σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformSigmaZeroEq
section
noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform

namespace GlobalTheory.HeckeTwo

lemma lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]

lemma norm_inv_ofReal_add_mul_I_sq (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * I)⁻¹ ^ 2‖ = (x ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma ofReal_add_ofReal_mul_I_ne_zero (x : ℝ) {y : ℝ} (hy : 0 < y) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem hTrans_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y =
    if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  intro ν y hy
  set g := GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) with hg
  have hw : ((y : ℂ) * I).im ≠ 0 := by simp [hy.ne']
  have hgc : Continuous g := GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel le_rfl hw
  have hgi : Integrable g := by
    rw [hg, lipschitzOneVariableKernel_two_eq_indicator hy, integrable_indicator_iff measurableSet_Ioi]
    exact GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg 1 (by simp; positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ∀ x : ℝ, 𝓕 g x = -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 := by
    intro x
    rw [hg, GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow 2 le_rfl even_two _ hw x]
    have hne := ofReal_add_ofReal_mul_I_ne_zero (-x) hy
    rw [zpow_neg, zpow_natCast]
    push_cast at hne ⊢
    have : (y : ℂ) * I - x = -(x : ℂ) + y * I := by ring
    rw [this]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hFi : Integrable (𝓕 g) := by
    have hb : Integrable (fun x : ℝ => ((4 * Real.pi ^ 2 * y ^ 2)⁻¹ : ℝ) * (1 + (x / y) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    · rw [show (𝓕 g) = fun x : ℝ => -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 from funext hF]
      exact Continuous.aestronglyMeasurable
        (continuous_const.mul ((((continuous_ofReal.comp continuous_neg).add continuous_const).inv₀
          (fun x => ofReal_add_ofReal_mul_I_ne_zero (-x) hy)).pow 2))
    · rw [hF, norm_mul, norm_neg, norm_inv, norm_mul, norm_pow, norm_inv_ofReal_add_mul_I_sq]
      simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, neg_sq]
      have : y ≠ 0 := hy.ne'
      field_simp <;> ring
  have hinv : 𝓕 (𝓕⁻ g) = g := hgc.fourier_fourierInv_eq hgi hFi
  have hphi : ∀ t : ℝ, phi 0 ((t : ℂ) + (y : ℂ) * I) = -4 * (Real.pi : ℂ) ^ 2 * 𝓕⁻ g t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg, hF, neg_neg]
    unfold phi
    rw [mul_zero, Complex.cpow_zero, mul_one]
    field_simp
  have hT : hTrans 0 ν y = -4 * (Real.pi : ℂ) ^ 2 * 𝓕 (𝓕⁻ g) ν := by
    unfold hTrans
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext t
    rw [hphi t, smul_eq_mul]
    push_cast
    ring_nf
  rw [hT, hinv, hg]
  simp only [GlobalTheory.LipschitzTR.phi1]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases hν : 0 < ν
  · rw [if_pos hν, if_pos hν, abs_of_pos hν]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · rw [if_neg hν, if_neg hν, mul_zero]

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermHasFDerivUpperHalfPlane
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fderiv_prod_coord {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℂ → ℂ) (L : ι → ℂ →L[ℝ] ℂ) (z : ι → ℂ)
    (hg : ∀ i, HasFDerivAt (g i) (L i) (z i)) :
    DifferentiableAt ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z ∧
    ∀ (j : ι) (v : ℂ), fderiv ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z (Pi.single j v) =
      L j v * ∏ i ∈ Finset.univ.erase j, g i (z i) := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun w : ι → ℂ => g i (w i))
      ((L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i)) z := fun i _ =>
    (hg i).comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h1
  refine ⟨h2.differentiableAt, fun j v => ?_⟩
  rw [h2.fderiv, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem hasFDerivAt_factor (c : ℂ) (a β : ℝ) (h : ℝ → ℂ) (h' : ℂ) (w : ℂ) (hh : HasDerivAt h h' (β * w.im)) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun u : ℂ => Complex.exp (c * ((a * u.re : ℝ) : ℂ)) * h (β * u.im)) L w ∧
      L 1 = c * (a : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h (β * w.im)) ∧
      L I = (β : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h') := by
  have e1 : HasFDerivAt (fun u : ℂ => ((a * u.re : ℝ) : ℂ)) (Complex.ofRealCLM.comp (a • Complex.reCLM)) w :=
    (Complex.ofRealCLM.comp (a • Complex.reCLM)).hasFDerivAt
  have e2 := (e1.const_mul c).cexp
  have e3 : HasFDerivAt (fun u : ℂ => β * u.im) (β • Complex.imCLM) w := (β • Complex.imCLM).hasFDerivAt
  have e4 := hh.hasFDerivAt.comp w e3
  refine ⟨_, e2.mul e4, ?_, ?_⟩
  · simp; ring
  · simp; ring

theorem termQ_fderiv : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  intro F _ _ b ν hb H σ hσ q z hz τ₀
  have hne : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ =>
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  choose L hL hL1 hLI using fun τ : Emb F => hasFDerivAt_factor (2 * (Real.pi : ℂ) * I) (τ ν * τ b) (τ b)
    (iteratedDeriv (q τ) (hTrans σ (τ ν))) _ (z τ) ((H (τ ν) (q τ) _ (hne τ)).1 σ hσ)
  obtain ⟨hd, hf⟩ := fderiv_prod_coord _ L z hL
  refine ⟨hd, ?_, ?_⟩
  · refine (hf τ₀ 1).trans ?_
    unfold termQ
    rw [hL1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)]
    ring
  · refine (hf τ₀ I).trans ?_
    unfold termQ
    rw [hLI, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), mul_assoc]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun τ hτ => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hτ)]

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensorStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  first | exact @GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | exact GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | (intros; apply GlobalTheory.FlatDescent.hilbert90_local_of_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBound
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

theorem normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hw, hn]
  nlinarith [sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]

theorem bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)

end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData), (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) = RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  first | (exact @GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (exact GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (intros; apply GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealsEqOfSpanIndependent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideals_eq_of_span_independent : ∀ (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)), J₁ ≤ J₂ → Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k)) → J₁ = J₂ := by
  first | (exact @GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (exact GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (intros; apply GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent  <;> assumption)
end

