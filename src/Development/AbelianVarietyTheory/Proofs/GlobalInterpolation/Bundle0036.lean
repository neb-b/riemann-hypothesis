module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacter
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRayClassLFunctionRealZeroFarFromOne
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem LFam.norm_deriv_F_le_near_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (z : ℂ)
    (hz : z ∈ Metric.closedBall (1 : ℂ) (1 / 4)) : ‖deriv (𝓕.F χ) z‖ ≤ 18000 * 𝓕.B := by
  obtain ⟨han, -, hbd, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  have hB : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have key : ∀ w ∈ Metric.closedBall z (1 / 10), 13 / 20 ≤ w.re ∧ ‖w‖ ≤ 27 / 20 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hz hw
    have h1 : ‖w - 1‖ ≤ 7 / 20 := by
      have : w - 1 = (w - z) + (z - 1) := by ring
      rw [this]
      linarith [norm_add_le (w - z) (z - 1)]
    constructor
    · have h2 := Complex.abs_re_le_norm (w - 1)
      have h3 := (abs_le.1 (h2.trans h1)).1
      simp only [sub_re, one_re] at h3
      linarith
    · have : w = (w - 1) + 1 := by ring
      rw [this]
      have h2 := norm_add_le (w - 1) 1
      rw [norm_one] at h2
      linarith
  have hd : DiffContOnCl ℂ (𝓕.F χ) (Metric.ball z (1 / 10)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num)]
    intro w hw
    have := (key w hw).1
    exact (han w (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt.differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (C := 1800 * 𝓕.B) (by norm_num : (0 : ℝ) < 1 / 10) hd
    (by
      intro w hw
      obtain ⟨h1, h2⟩ := key w (Metric.sphere_subset_closedBall hw)
      have h3 := hbd w (by linarith)
      have h4 : (‖w‖ + 1) ^ 2 ≤ 6 := by nlinarith [norm_nonneg w]
      nlinarith)
  linarith [show 1800 * 𝓕.B / (1 / 10) = 18000 * 𝓕.B by ring]

theorem LFam.real_zero_far_from_one : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  obtain ⟨A, c, hA, hc, h⟩ := _root_.GlobalTheory.Hk.RealChar.norm_F_one_ge
  refine ⟨A + 1, c / 18000, by linarith, by positivity, ?_⟩
  intro 𝓕 χ β hχ hβ h0
  have hB : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have hβ1 : β ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ β (by simpa using hlt)).2.2.1 h0
  obtain ⟨han, -, -, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  have hn : ‖(1 : ℂ) - β‖ = 1 - β := by
    rw [show (1 : ℂ) - β = ((1 - β : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hmv := (convex_closedBall (1 : ℂ) (1 / 4)).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := 𝓕.F χ)
    (C := 18000 * 𝓕.B) (x := (β : ℂ)) (y := 1)
    (by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h3 := (abs_le.1 ((Complex.abs_re_le_norm (z - 1)).trans hz)).1
      simp only [sub_re, one_re] at h3
      exact (han z (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt)
    (fun z hz => 𝓕.norm_deriv_F_le_near_one χ z hz)
    (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hn]; linarith)
    (Metric.mem_closedBall_self (by norm_num))
  rw [h0, sub_zero, hn] at hmv
  have h1 := (h 𝓕 χ hχ).trans hmv
  have hp : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos hB A
  rw [Real.rpow_add hB, Real.rpow_one, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hp] at h1
  nlinarith

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiProductOfThetaWeber
section
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

namespace GlobalTheory.ThetaWeberRoad

theorem jacobiProduct_of_thetaWeber {τ : UpperHalfPlane} (hTW : ThetaWeber τ)
    (hw : weberF τ * weberF₁ τ * weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ)) : JacobiProduct τ := by
  obtain ⟨h1, h2, h3⟩ := hTW
  unfold JacobiProduct
  rw [h1, h2, h3]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (ModularForm.eta (τ : ℂ)) ^ 3 *
    (weberF τ * weberF₁ τ * weberF₂ τ + ((Real.sqrt 2 : ℝ) : ℂ)) * hw +
    ModularForm.eta (τ : ℂ) ^ 3 * hs

theorem thetaWeberStatement_of (hTL : Formalism.L2.Th1.F.ThetaLine) (hSB : Formalism.L2.Th1.F.SgStarBasic)
    (hSA : Formalism.L2.Th1.F.SgStarAdd) : ThetaWeberStatement := by
  have hTW := GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct _root_.GlobalTheory.JacobiTriple.tripleProduct
  have hJ : ∀ τ : UpperHalfPlane, JacobiProduct τ := fun τ ↦
    jacobiProduct_of_thetaWeber (hTW τ) (GlobalTheory.T.weberFunction_product_eq_sqrt_two τ)
  have hH := _root_.GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of hSA (_root_.GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar hTL hSB) (_root_.GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero _root_.GlobalTheory.JacobiTriple.tripleProduct) hJ
  intro τ
  exact ⟨hH τ, hJ τ, hTW τ, _root_.GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff τ (hH τ) (hJ τ) (hTW τ)⟩

end GlobalTheory.ThetaWeberRoad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormula
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.HkLocal

theorem analyticOrderNatAt_comp_affine (g : ℂ → ℂ) (c ρ w : ℂ) (hρ : ρ ≠ 0) :
    analyticOrderNatAt (fun z => g (c + ρ * z)) w = analyticOrderNatAt g (c + ρ * w) := by
  unfold analyticOrderNatAt
  congr 1
  have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ w := by
    simpa using ((hasDerivAt_id w).const_mul ρ).const_add c
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + ρ * z) (z₀ := w)
    (by fun_prop) (by rw [hd.deriv]; exact hρ)
  exact h

theorem logDeriv_local : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (5/7) (6/7) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨12 * C, by positivity, ?_⟩
  intro 𝓕 χ t
  obtain ⟨han, hLS, hgr, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  set c : ℂ := 5 / 4 + t * I with hc
  have hcre : c.re = 5 / 4 := by simp [hc]
  have hcn : ‖c‖ ≤ 5 / 4 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hB : 4 ≤ 𝓕.B := 𝓕.B_ge
  have ht : 0 ≤ |t| := abs_nonneg t
  set ρ : ℂ := 7 / 10 with hρ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; norm_num
  have hρn : ‖ρ‖ = 7 / 10 := by simp [hρ]
  have hre : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 11 / 20 ≤ (c + ρ * z).re ∧ ‖ρ * z‖ ≤ 7 / 10 := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have h1 : ‖ρ * z‖ ≤ 7 / 10 := by rw [norm_mul, hρn]; linarith
    have := (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
    refine ⟨?_, h1⟩
    rw [add_re, hcre]; linarith
  have hf : AnalyticOnNhd ℂ (fun z => 𝓕.F χ (c + ρ * z)) (Metric.closedBall 0 1) := by
    intro z hz
    have h1 : AnalyticAt ℂ (𝓕.F χ) (c + ρ * z) :=
      han _ (show 1 / 2 < (c + ρ * z).re by linarith [(hre z hz).1])
    exact AnalyticAt.comp (g := 𝓕.F χ) (f := fun z => c + ρ * z) h1 (by fun_prop)
  have hlow : 1 / 100 ≤ ‖𝓕.F χ (c + ρ * 0)‖ := by
    have h1 : 1 < c.re := by rw [hcre]; norm_num
    have h2 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ c h1).2.1
    rw [hcre] at h2
    rw [mul_zero, add_zero, (hLS c h1).2, norm_mul]
    have h3 : 1 / 4 ≤ ‖(if χ = 1 then c - 1 else 1 : ℂ)‖ := by
      split_ifs
      · have := (le_abs_self _).trans (Complex.abs_re_le_norm (c - 1))
        rw [sub_re, hcre, one_re] at this
        linarith
      · norm_num
    have h4 : 1 / 25 ≤ ‖LSeries (𝓕.aChi χ) c‖ := le_trans (by norm_num) h2
    calc (1 / 100 : ℝ) = (1 / 4) * (1 / 25) := by norm_num
      _ ≤ _ := by gcongr
  have hf0 : 𝓕.F χ (c + ρ * 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖𝓕.F χ (c + ρ * z)‖ ≤ 300 * 𝓕.B * (|t| + 3) ^ 2 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hre z hz
    have hn : ‖c + ρ * z‖ + 1 ≤ |t| + 3 := by
      have := norm_add_le c (ρ * z)
      linarith
    refine (hgr _ h1).trans ?_
    gcongr
  obtain ⟨⟨hfin, hcnt⟩, hb⟩ := H _ _ hf hf0 hM
  have hset : {w : ℂ | ‖w - c‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0} =
      (fun z => c + ρ * z) '' {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      have e : c + ρ * ((w - c) / ρ) = w := by field_simp; ring
      refine ⟨(w - c) / ρ, ⟨?_, by rw [e]; exact h2⟩, e⟩
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      simp only [add_sub_cancel_left, norm_mul, hρn]
      linarith
  have hinj : Set.InjOn (fun z => c + ρ * z) {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} :=
    fun a _ b _ h => mul_left_cancel₀ hρ0 (add_left_cancel h)
  have hlog : 1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖) ≤ 8 * 𝓕.ell t ∧
      0 ≤ 𝓕.ell t := by
    unfold LFam.ell
    set X : ℝ := 𝓕.B * (|t| + 2) with hX
    have hX8 : 8 ≤ X := by rw [hX]; nlinarith
    have hl1 : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (show 0 < X by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hp : 0 < ‖𝓕.F χ (c + ρ * 0)‖ := norm_pos_iff.2 hf0
    have h8 : 300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖ ≤ X ^ 7 := by
      rw [div_le_iff₀ hp]
      have hX0 : 0 ≤ X := by linarith
      have h5 : (8 : ℝ) ^ 5 ≤ X ^ 5 := by gcongr
      have h6 : 4 * (𝓕.B * (|t| + 2) ^ 2) ≤ X ^ 2 := by
        rw [hX, mul_pow, pow_two 𝓕.B, mul_assoc]
        gcongr
      have h7 : (|t| + 3) ^ 2 ≤ (9 / 4) * (|t| + 2) ^ 2 := by nlinarith
      have h9 : 𝓕.B * (|t| + 3) ^ 2 ≤ 𝓕.B * ((9 / 4) * (|t| + 2) ^ 2) := by gcongr
      have h10 : 0 ≤ X ^ 2 := by positivity
      calc 300 * 𝓕.B * (|t| + 3) ^ 2 ≤ 8 ^ 5 * X ^ 2 * (1 / 100) := by nlinarith
        _ ≤ X ^ 5 * X ^ 2 * ‖𝓕.F χ (c + ρ * 0)‖ := by gcongr
        _ = _ := by ring
    have h9 := Real.log_le_log (by positivity) h8
    rw [Real.log_pow] at h9
    push_cast at h9
    constructor <;> linarith
  obtain ⟨hlog, hell⟩ := hlog
  have hCl : C * (1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖)) ≤
      C * (8 * 𝓕.ell t) := by gcongr
  have hCe : 0 ≤ C * 𝓕.ell t := by positivity
  rw [hset]
  refine ⟨hfin.image _, ?_, ?_⟩
  · rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0] at hcnt
    refine hcnt.trans (hCl.trans ?_)
    linarith
  · intro s hs hLs
    have e : c + ρ * ((s - c) / ρ) = s := by field_simp; ring
    have hz : ‖(s - c) / ρ‖ ≤ 5 / 7 := by
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    have hb' := hb ((s - c) / ρ) hz (by simpa only [e] using hLs)
    have hsre : 1 / 2 < s.re := by
      have := (hre ((s - c) / ρ) (by simpa only [mem_closedBall_zero_iff] using hz.trans (by norm_num))).1
      rw [e] at this
      linarith
    have hder : deriv (fun z => 𝓕.F χ (c + ρ * z)) ((s - c) / ρ) = ρ * deriv (𝓕.F χ) s := by
      have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ ((s - c) / ρ) := by
        simpa using ((hasDerivAt_id ((s - c) / ρ)).const_mul ρ).const_add c
      have h1 : HasDerivAt (𝓕.F χ) (deriv (𝓕.F χ) s) (c + ρ * ((s - c) / ρ)) := by
        rw [e]; exact (han s hsre).differentiableAt.hasDerivAt
      have := (HasDerivAt.comp ((s - c) / ρ) h1 hd).deriv
      rw [mul_comm] at this
      exact this
    rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0, hder, e] at hb'
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hb' ⊢
    have e2 : ∀ w : ℂ, (analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / ((s - c) / ρ - w) =
        ρ * ((analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / (s - (c + ρ * w))) := by
      intro w
      have : s - (c + ρ * w) = ρ * ((s - c) / ρ - w) := by field_simp; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hρ0]
    simp only [e2] at hb'
    rw [← Finset.mul_sum, mul_div_assoc, ← mul_sub, norm_mul, hρn] at hb'
    have := hb'.trans hCl
    linarith

end GlobalTheory.HkLocal
end

