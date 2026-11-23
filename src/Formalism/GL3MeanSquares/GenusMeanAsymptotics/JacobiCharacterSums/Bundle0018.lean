module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectA
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0003
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

variable {M : ℕ} [NeZero M]

theorem exLF_of_ne {χ : DirichletCharacter ℂ M} (h : χ ≠ 1) : exLF χ = DirichletCharacter.LFunction χ := by
  unfold exLF; rw [if_neg h]

theorem exLF_one_char : exLF (1 : DirichletCharacter ℂ M) = DirichletCharacter.LFunctionTrivChar₁ M := by
  unfold exLF; rw [if_pos rfl]

theorem exLF_one_char_apply {s : ℂ} (hs : s ≠ 1) :
    exLF (1 : DirichletCharacter ℂ M) s = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s := by
  rw [exLF_one_char, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]

theorem exLF_differentiable (χ : DirichletCharacter ℂ M) : Differentiable ℂ (exLF χ) := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.differentiable_LFunctionTrivChar₁ M
  · rw [exLF_of_ne h]; exact DirichletCharacter.differentiable_LFunction h

theorem exLF_one_ne_zero (χ : DirichletCharacter ℂ M) : exLF χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero M
  · rw [exLF_of_ne h]; exact DirichletCharacter.LFunction_apply_one_ne_zero h

theorem exLF_eq_zero_iff (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    exLF χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char_apply hs, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero_of_ne hs), Or.inr⟩
  · rw [exLF_of_ne h]

theorem isLZero_iff_exLF (χ : DirichletCharacter ℂ M) (s : ℂ) : IsLZero χ s ↔ exLF χ s = 0 := by
  unfold IsLZero
  by_cases hs : s = 1
  · subst hs
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd h2 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (by simp))
    · intro h; exact absurd h (exLF_one_ne_zero χ)
  · rw [exLF_eq_zero_iff χ hs]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr hs, h⟩⟩

theorem exLF_re_lt_one (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : exLF χ s = 0) : s.re < 1 := by
  by_contra hlt
  obtain ⟨h1, h2⟩ := (isLZero_iff_exLF χ s).2 hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (not_lt.1 hlt) h2

theorem negLD_eq_exLF (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) (h0 : exLF χ s ≠ 0) :
    negLD χ s = (if χ = 1 then 1 / (s - 1) else 0) - deriv (exLF χ) s / exLF χ s := by
  unfold negLD
  by_cases h : χ = 1
  · subst h
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s ≠ 0 :=
      fun hz => h0 ((exLF_eq_zero_iff _ hs).2 hz)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
    rw [if_pos rfl, exLF_one_char_apply hs, exLF_one_char,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    field_simp
    ring
  · rw [if_neg h, exLF_of_ne h, zero_sub]

theorem exLF_deriv_ne_zero (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) : deriv (exLF χ) ρ ≠ 0 := by
  by_cases h : χ = 1
  · subst h
    have hs : ρ ≠ 1 := by
      rintro rfl; exact exLF_one_ne_zero _ hρ
    have hL := (exLF_eq_zero_iff _ hs).1 hρ
    rw [exLF_one_char, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    rw [hL, add_zero]
    exact mul_ne_zero (sub_ne_zero_of_ne hs) hd
  · rw [exLF_of_ne h]; exact hd

theorem exLF_analyticAt (χ : DirichletCharacter ℂ M) (z : ℂ) : AnalyticAt ℂ (exLF χ) z :=
  (exLF_differentiable χ).analyticAt z

theorem exLF_order_ne_top (χ : DirichletCharacter ℂ M) (ρ : ℂ) : analyticOrderAt (exLF χ) ρ ≠ ⊤ := by
  intro h
  have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (exLF_analyticAt χ)).1 h
  exact exLF_one_ne_zero χ (by rw [this]; rfl)

theorem exOrd_pos (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) : 1 ≤ exOrd χ ρ := by
  unfold exOrd
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have h1 : analyticOrderAt (exLF χ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (exLF_order_ne_top χ ρ), h]; rfl
  exact ((exLF_analyticAt χ ρ).analyticOrderAt_eq_zero.1 h1) hρ

theorem exOrd_eq_one (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) (hd : deriv (exLF χ) ρ ≠ 0) :
    exOrd χ ρ = 1 := by
  unfold exOrd analyticOrderNatAt
  rw [(exLF_analyticAt χ ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hd]
  rfl

theorem exLF_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  have h1 : ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) := by
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (by omega : 1 ≤ p)
      · simp only [Complex.neg_re]; linarith
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ ≤ p := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
  have h2 : ∏ p ∈ M.primeFactors, (p : ℝ) ≤ M := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
    calc ∏ p ∈ M.primeFactors, (p : ℝ) = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ M := by exact_mod_cast this
  exact h1.trans h2

theorem exLF_growth : ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ), 1 / 2 ≤ s.re →
    ‖exLF χ s‖ ≤ C * M * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  refine ⟨max C0 6, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro M _ χ s hs
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  by_cases h : χ = 1
  · subst h
    have h6 : 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      gcongr; exact le_max_right _ _
    refine le_trans ?_ h6
    by_cases hs1 : s = 1
    · subst hs1
      rw [exLF_one_char]
      simp only [Function.update_self]
      have := exLF_prod_le M 1 (by norm_num)
      have he : ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [Complex.cpow_neg_one]
      rw [he] at this
      refine this.trans ?_
      rw [norm_one]; nlinarith
    · rw [exLF_one_char_apply hs1]
      have hz := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := M) hs1
      simp only [DirichletCharacter.LFunctionTrivChar] at hz
      rw [hz]
      have hP := exLF_prod_le M s hs
      have hZ := Formalism.ZF.growthBound s (by linarith) hs1
      have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hs1)
      have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ := by rw [norm_one]; ring
      have hre : 1 / s.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hA : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 6 * (1 + ‖s‖) ^ 2 := by
        calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
          _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
          _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
          _ ≤ 6 * (1 + ‖s‖) ^ 2 := by nlinarith
      calc ‖(s - 1) * ((∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s)‖
          = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ M * (6 * (1 + ‖s‖) ^ 2) := by gcongr
        _ = 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 := by ring
  · rw [exLF_of_ne h]
    have h1 := hC0 M χ h s hs
    have h2 : C0 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) := by
      gcongr; exact le_max_left _ _
    have h3 : max C0 6 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      have hc : 0 ≤ max C0 6 * M := by
        have : (0 : ℝ) ≤ max C0 6 := le_trans (by norm_num) (le_max_right _ _)
        positivity
      have : (1 + ‖s‖) ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hc
    linarith

theorem exLF_lower (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ ‖exLF χ s‖ := by
  have hI := inverseBound M χ s hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := norm_pos_iff.2 hne
  have hq : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    have h1 : (s.re / (s.re - 1))⁻¹ ≤ (‖DirichletCharacter.LFunction χ s‖⁻¹)⁻¹ :=
      inv_anti₀ (inv_pos.2 hpos) hI
    rwa [inv_inv, inv_div] at h1
  by_cases h : χ = 1
  · subst h
    rw [exLF_one_char_apply hs1, norm_mul]
    exact mul_le_mul (min_le_right _ _) hL hq.le (norm_nonneg _)
  · rw [exLF_of_ne h]
    calc min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ 1 * ((s.re - 1) / s.re) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le
      _ ≤ _ := by rw [one_mul]; exact hL

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRect
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exr_abs_le {a p q : ℝ} (h1 : p ≤ a) (h2 : a ≤ q) : |a| ≤ |p| + |q| :=
  abs_le.2 ⟨by linarith [neg_abs_le p, abs_nonneg q], by linarith [le_abs_self q, abs_nonneg p]⟩

theorem ex_rect_logDeriv (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (y : ℝ) (hy : 0 < y)
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (f ρ = 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁))
    (hedge : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → f w = 0 →
      x₀ < w.re ∧ w.re < x₁ ∧ y₀ < w.im ∧ w.im < y₁) :
    Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (-(deriv f 1 / f 1) * y - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ) := by
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = |x₀ - 1| + |x₁ - 1| + |y₀| + |y₁| + 1 := ⟨_, rfl⟩
  have hR₁ : 0 < R₁ := by rw [hR₁def]; positivity
  obtain ⟨Zb, m, h, hZb, hm, hh, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f 1 (R₁ + 1) R₁ hR₁ (by linarith) hf.differentiableOn hf1
  have hrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w a1 a2 a3 a4
    rw [Metric.mem_ball, dist_eq_norm]
    have e1 := Complex.norm_le_abs_re_add_abs_im (w - 1)
    have e2 : |(w - 1).re| ≤ |x₀ - 1| + |x₁ - 1| := by
      rw [sub_re, one_re]; exact exr_abs_le (by linarith) (by linarith)
    have e3 : |(w - 1).im| ≤ |y₀| + |y₁| := by
      rw [sub_im, one_im, sub_zero]; exact exr_abs_le a3 a4
    linarith
  have hball : Metric.ball (1 : ℂ) R₁ ⊆ Metric.closedBall 1 R₁ := Metric.ball_subset_closedBall
  have hSsub : Metric.ball (1 : ℂ) (R₁ + 1) ⊆ Metric.closedBall 1 (R₁ + 1) := Metric.ball_subset_closedBall
  have hR1S : Metric.ball (1 : ℂ) R₁ ⊆ Metric.ball 1 (R₁ + 1) := Metric.ball_subset_ball (by linarith)
  have hhS : DifferentiableOn ℂ h (Metric.ball 1 (R₁ + 1)) := hh.mono hSsub
  have hfacS : ∀ z ∈ Metric.ball (1 : ℂ) (R₁ + 1), f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    fun z hz => hfac z (hSsub hz)
  have hZin : ∀ ρ ∈ Z, ρ ∈ Metric.ball (1 : ℂ) R₁ := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hrect ρ a1.le a2.le a3.le a4.le
  have hZsub : Z ⊆ Zb := by
    intro ρ hρ
    exact (hZb ρ).2 ⟨hball (hZin ρ hρ), ((hZ ρ).1 hρ).1⟩
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := fun ρ hρ =>
    exr_ord f h Zb m _ Metric.isOpen_ball hhS hfacS ρ (hZsub hρ) (hR1S (hZin ρ hρ))
      (hh0 ρ (hball (hZin ρ hρ)))
  have h1Z : (1 : ℂ) ∉ Z := fun h => hf1 ((hZ 1).1 h).1
  have hZne0 : ∀ ρ ∈ Z, ρ ≠ 0 := by
    intro ρ hρ h0; have := ((hZ ρ).1 hρ).2.1; rw [h0, zero_re] at this; linarith
  have hZne1 : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h1 => h1Z (h1 ▸ hρ)

  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = Metric.ball (1 : ℂ) R₁ \ (((Zb \ Z : Finset ℂ) : Set ℂ) ∪ {0}) :=
    ⟨_, rfl⟩
  have hU : IsOpen U := by
    rw [hUdef]
    exact Metric.isOpen_ball.sdiff ((Finset.finite_toSet _).union (Set.finite_singleton 0)).isClosed
  have hUrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ U := by
    intro w a1 a2 a3 a4
    rw [hUdef]
    refine ⟨hrect w a1 a2 a3 a4, ?_⟩
    rintro (hw | hw)
    · rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_coe] at hw
      have hfw : f w = 0 := ((hZb w).1 hw.1).2
      obtain ⟨b1, b2, b3, b4⟩ := hedge w a1 a2 a3 a4 hfw
      exact hw.2 ((hZ w).2 ⟨hfw, b1, b2, b3, b4⟩)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, zero_re] at a1; linarith
  have hUball : ∀ w ∈ U, w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w hw; rw [hUdef] at hw; exact hw.1
  have hUne0 : ∀ w ∈ U, w ≠ 0 := by
    intro w hw h0; rw [hUdef] at hw; exact hw.2 (Or.inr h0)
  have hUZb : ∀ w ∈ U, w ∉ Z → w ∉ Zb := by
    intro w hw hwZ hwZb; rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff]; exact ⟨hwZb, hwZ⟩))
  have h1U : (1 : ℂ) ∈ U := hUrect 1 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZU : ∀ ρ ∈ Z, ρ ∈ U := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hUrect ρ a1.le a2.le a3.le a4.le

  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun w => (y : ℂ) ^ w / w := ⟨_, rfl⟩
  obtain ⟨Lf, hLdef⟩ : ∃ Lf : ℂ → ℂ,
      Lf = fun w => deriv h w / h w + ∑ ρ ∈ Zb \ Z, (m ρ : ℂ) / (w - ρ) := ⟨_, rfl⟩
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hφU : DifferentiableOn ℂ φ U := by
    intro w hw
    rw [hφdef]
    exact ((differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id
      (hUne0 w hw)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ Lf U := by
    intro w hw
    have hwb := hR1S (hUball w hw)
    have hN : Metric.ball (1 : ℂ) (R₁ + 1) ∈ nhds w := Metric.isOpen_ball.mem_nhds hwb
    have hd1 : DifferentiableAt ℂ (deriv h) w :=
      ((hhS.deriv Metric.isOpen_ball) w hwb).differentiableAt hN
    have hd2 : DifferentiableAt ℂ h w := (hhS w hwb).differentiableAt hN
    have hhw : h w ≠ 0 := hh0 w (hball (hUball w hw))
    rw [hLdef]
    refine (DifferentiableAt.add (hd1.div hd2 hhw) ?_).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun ρ hρ => ?_
    refine (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) ?_
    rw [Finset.mem_sdiff] at hρ
    intro h0; rw [sub_eq_zero] at h0
    rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff, h0]; exact ⟨hρ.1, hρ.2⟩))
  have hLD : ∀ w ∈ U, w ∉ Z → deriv f w / f w = (∑ ρ ∈ Z, (m ρ : ℂ) / (w - ρ)) + Lf w := by
    intro w hw hwZ
    rw [exr_logDeriv f h Zb m _ Metric.isOpen_ball hhS hfacS w (hR1S (hUball w hw)) (hUZb w hw hwZ)
      (hh0 w (hball (hUball w hw))), hLdef, ← Finset.sum_sdiff hZsub]
    ring
  have hk : ∀ w, exKer y w = φ w / (w - 1) := fun w => by rw [hφdef, exKer, div_div]
  have hb1 : ∃ b : ℂ → ℂ, b 1 = -(deriv f 1 / f 1) * y ∧ ∀ ρ ∈ Z, b ρ = -(m ρ : ℂ) * exKer y ρ :=
    ⟨fun p => if p = 1 then -(deriv f 1 / f 1) * y else -(m p : ℂ) * exKer y p, by simp,
      fun ρ hρ => by simp [hZne1 ρ hρ]⟩
  obtain ⟨b, hb1, hbρ⟩ := hb1
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : ℂ → ℂ, G₀ = fun w => -dslope (fun z => Lf z * φ z) 1 w -
      ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := ⟨_, rfl⟩
  have hG₀U : DifferentiableOn ℂ G₀ U := by
    rw [hG₀def]
    refine DifferentiableOn.sub ((differentiableOn_dslope (hU.mem_nhds h1U)).2 (hLU.mul hφU)).neg ?_
    refine DifferentiableOn.fun_sum fun ρ hρ => ?_
    exact (differentiableOn_const _).mul (((differentiableOn_dslope (hU.mem_nhds (hZU ρ hρ))).2 hφU).sub
      ((differentiableOn_dslope (hU.mem_nhds h1U)).2 hφU))
  have hφw : ∀ z, φ z = (y : ℂ) ^ z / z := fun z => by rw [hφdef]
  have hφ1 : φ 1 = y := by rw [hφw]; simp
  have hkey : ∀ w ∈ U, w ∉ insert 1 Z →
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) = G₀ w := by
    intro w hw hwP
    rw [Finset.mem_insert, not_or] at hwP
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hwP.1
    have hw0 := hUne0 w hw
    have hwρ : ∀ ρ ∈ Z, w - ρ ≠ 0 := fun ρ hρ h0 => hwP.2 (sub_eq_zero.1 h0 ▸ hρ)
    have hC : ∑ ρ ∈ Z, b ρ / (w - ρ) = ∑ ρ ∈ Z, -(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1))) / (w - ρ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, exKer]
    have hD : ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) =
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1)) :=
      Finset.sum_congr rfl fun ρ hρ => by
        rw [dslope_of_ne _ (sub_ne_zero.1 (hwρ ρ hρ)), dslope_of_ne _ hwP.1, slope_def_field,
          slope_def_field, hφ1, hφw, hφw]
    have hrel : ∑ ρ ∈ Z, (-((m ρ : ℂ) / (w - ρ)) * ((y : ℂ) ^ w / w / (w - 1)) +
        (m ρ : ℂ) / (1 - ρ) * y / (w - 1) - (-(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1)))) / (w - ρ) +
        (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1))) = 0 :=
      Finset.sum_eq_zero fun ρ hρ => exr_term _ _ _ _ _ _ hw0 hw1 (hwρ ρ hρ) (hZne0 ρ hρ)
        (sub_ne_zero.2 (hZne1 ρ hρ))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hrel
    have hG₀w : G₀ w = -dslope (fun z => Lf z * φ z) 1 w -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := by rw [hG₀def]
    rw [hG₀w, hD, Finset.sum_insert h1Z, hC, hb1, dslope_of_ne _ hwP.1, slope_def_field, hLD w hw hwP.2,
      hLD 1 h1U h1Z, hk w, hφ1, hφw w]
    linear_combination hrel
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun w => if w ∈ insert 1 Z then G₀ w else
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) := ⟨_, rfl⟩
  have hGU : DifferentiableOn ℂ G U := by
    refine hG₀U.congr fun w hw => ?_
    rw [hGdef]
    by_cases hwP : w ∈ insert 1 Z
    · simp only [if_pos hwP]
    · simp only [if_neg hwP]; exact hkey w hw hwP
  have hPin : ∀ p ∈ insert 1 Z, x₀ < p.re ∧ p.re < x₁ ∧ y₀ < p.im ∧ p.im < y₁ := by
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with hp | hp
    · subst hp; simp; exact ⟨hx₀1, hx₁, hy₀, hy₁⟩
    · exact ((hZ p).1 hp).2
  have hsub : (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    exact hUrect w hw.1.1 hw.1.2 hw.2.1 hw.2.2
  have hres := Formalism.FX.rectangle_residue (fun w => -(deriv f w / f w) * exKer y w) G (insert 1 Z) b
    x₀ x₁ y₀ y₁ (by linarith) (by linarith) hPin ⟨U, hU, hsub, hGU⟩ (fun w hw => by
      rw [hGdef]; simp only [if_neg hw]; ring)
  have hsum : ∑ ρ ∈ Z, b ρ = -∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, hord ρ hρ, neg_mul]
  rw [show Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
    Formalism.FX.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ from rfl, hres,
    Finset.sum_insert h1Z, hb1, hsum]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

