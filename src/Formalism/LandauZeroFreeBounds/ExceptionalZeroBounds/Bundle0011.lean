module

public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0008

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
section
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma dirichlet_character_lseries_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s := by
  refine (LSeriesSummable_congr s (fun {n} hn => ?_)).mpr (χ.LSeriesSummable_of_one_lt_re hs)
  simp [toArithmeticFunction, hn]

lemma dirichlet_character_lseries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s

set_option backward.isDefEq.respectTransparency.types false in
lemma lseries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    exact (LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs),
    dirichlet_character_lseries_eq χ hs]
  congr 1
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => by simp [hn]) s

theorem dirichlet_product_coefficients : BqCoeff := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 hψ
  set f : ArithmeticFunction ℂ := DirichletCharacter.zetaMul χ₁ *
    (toArithmeticFunction (fun m : ℕ => χ₂ (m : ZMod q₂)) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) with hf

  have hvals : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 →
      ∀ x, χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
    intro N χ hχ x
    by_cases hx : IsUnit x
    · have h := congrArg (fun φ : DirichletCharacter ℂ N => φ x) hχ
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hx] at h
      have h' : χ x * χ x = 1 := by rw [← sq]; exact h
      rcases (mul_self_eq_one_iff).mp h' with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · exact Or.inl (MulChar.map_nonunit χ hx)
  have hmul : f.IsMultiplicative :=
    (DirichletCharacter.isMultiplicative_zetaMul χ₁).mul
      ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂).mul
        (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))
  have hswap : f = DirichletCharacter.zetaMul χ₂ *
      (toArithmeticFunction (fun m : ℕ => χ₁ (m : ZMod q₁)) *
        toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) := by
    simp only [hf, DirichletCharacter.zetaMul]
    ring
  have hψ' : ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₂ (n : ZMod q₂) * χ₁ (n : ZMod q₁) := by
    intro n
    rw [hψ n, mul_comm]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k) := by
    intro p k hp
    rcases hvals χ₂ h2 (p : ZMod q₂) with h | h | h
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inl h) k
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inl h)) k
    · rcases hvals χ₁ h1 (p : ZMod q₁) with h' | h' | h'
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inl h') k
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inr (Or.inl h')) k
      · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inr ⟨h, h'⟩)) k
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
      exact Finset.prod_nonneg fun p hp =>
        hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))
  have hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (⇑f) s := fun s hs =>
    ArithmeticFunction.LSeriesSummable_mul (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs))
  refine ⟨⇑f, hnn, hmul.map_one, ?_, ?_⟩
  · have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1)
      (fun y hy => hsum y (by simpa using hy))
    simpa using this
  · intro s hs
    rw [Fbq, ArithmeticFunction.LSeries_mul' (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs)),
      ArithmeticFunction.LSeries_mul' (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs),
      lseries_zetaMul_eq χ₁ hs, dirichlet_character_lseries_eq χ₂ hs, dirichlet_character_lseries_eq ψ hs]
    ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ChebyshevCharacterExplicitGeneral
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 1000000 in
theorem chebyshev_character_explicit_general (hP : PerronChi) (hRS : RectShiftChi) (c₁ C C₀ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 20) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (hχ : χ ≠ 1)
    (hE : ExcZeros c₁ χ B)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T L : ℝ) (hy : 2 ≤ y) (hT : 1 ≤ T) (hL : Real.log ((q : ℝ) * (T + 2)) = L) :
    ∃ σ₁ : ℝ, σ₁ ≤ 1 - c₁ / (4 * L) ∧
      ‖Schi χ y - negLD χ 1 * y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T)
        + y ^ σ₁ * (8 * L / c₁) := by
  obtain ⟨hBc, hBz, hBall⟩ := hE
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) ≤ y := by linarith
  have hy1' : (1:ℝ) < y := by linarith
  have hlog2 : (1:ℝ) / 2 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  have hlogy2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : (1:ℝ) / 2 < Real.log y := by linarith
  have hlogy : 0 < Real.log y := by linarith
  have hlogyne : Real.log y ≠ 0 := hlogy.ne'
  have hT0 : (0:ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast hq
  have hL2 : Real.log 2 ≤ L := by
    rw [← hL]
    exact Real.log_le_log (by norm_num) (by nlinarith)
  have hLh : (1:ℝ) / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hc₁ne : c₁ ≠ 0 := hc₁.ne'
  have ha : 0 < c₁ / L := div_pos hc₁ hL0
  have haL : c₁ / L * L = c₁ := by field_simp
  have ha' : c₁ / L ≤ 1 / 10 := by nlinarith
  have e3 : c₁ / (3 * L) = c₁ / L / 3 := by rw [mul_comm 3 L, ← div_div]
  have e4 : c₁ / (4 * L) = c₁ / L / 4 := by rw [mul_comm 4 L, ← div_div]
  have e2 : c₁ / 2 / L = c₁ / L / 2 := div_right_comm c₁ 2 L
  have h2ε : 2 / (c₁ / (4 * L)) = 8 * L / c₁ := by rw [div_div_eq_mul_div]; ring
  have h1δ : 1 / (c₁ / (24 * L)) = 24 * L / c₁ := one_div_div _ _
  obtain ⟨σ₁, hσ₁c, hσ₁B⟩ := exists_contour_avoiding_real_zero B hBc L c₁ hL0 hc₁
  rw [e3, e4] at hσ₁c
  have hσ₁b : 1 - c₁ / L / 3 ≤ σ₁ ∧ σ₁ ≤ 1 - c₁ / L / 4 := by
    rcases hσ₁c with h | h <;> rw [h] <;> constructor <;> linarith
  obtain ⟨hσ₁lo, hσ₁up⟩ := hσ₁b
  refine ⟨σ₁, by rw [e4]; exact hσ₁up, ?_⟩
  have hσ₁lt1 : σ₁ < 1 := by linarith
  have hσ₁pos : 0 < σ₁ := by linarith
  have hhalf : 1 / 2 ≤ σ₁ := by linarith
  have hgap : c₁ / (4 * L) ≤ 1 - σ₁ := by rw [e4]; linarith
  have hσ₁reg : 1 - c₁ / 2 / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁ := by
    rw [hL, e2]; linarith

  obtain ⟨σ₀, hσ₀e⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log y := ⟨_, rfl⟩
  have hinv : 1 / Real.log y * Real.log y = 1 := by field_simp
  have hinvpos : 0 < 1 / Real.log y := div_pos one_pos hlogy
  have hinv2 : 1 / Real.log y < 2 := by nlinarith
  have hσ₀gt : 1 < σ₀ := by rw [hσ₀e]; linarith
  have hσσ : σ₁ ≤ σ₀ := by linarith
  have hσdiff : |σ₀ - σ₁| ≤ 3 := by
    rw [abs_of_nonneg (by linarith), hσ₀e]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := by
    rw [hσ₀e, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hlogyne, mul_comm]

  have hB₁ : ∀ β ∈ B.filter (fun β => σ₁ < β),
      σ₁ < β ∧ β < σ₀ ∧ deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    obtain ⟨-, -, hz, hd⟩ := hBz β hβ.1
    refine ⟨hβ.2, ?_, hd⟩
    have hβ1 : β < 1 := by
      by_contra hc
      push_neg at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hc) hz
    linarith
  have hB₁z : ∀ β ∈ B.filter (fun β => σ₁ < β), DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    exact (hBz β hβ.1).2.2.1
  have hzer : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w = 0 → ∃ β ∈ B.filter (fun β => σ₁ < β), w = (β : ℂ) := by
    intro w h1 _ h3 h4
    have hreg : InRegion c₁ q w := by
      unfold InRegion
      have hm := log_analytic_conductor_mono q w.im T h3
      rw [hL] at hm
      have hpos := log_conductor_pos_real q w.im
      have key : c₁ / L ≤ c₁ / Real.log ((q : ℝ) * (|w.im| + 2)) := by
        rw [div_eq_mul_one_div c₁ L, div_eq_mul_one_div c₁ (Real.log ((q : ℝ) * (|w.im| + 2)))]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hm) hc₁.le
      linarith
    obtain ⟨β, hβB, hwβ⟩ := hBall w hreg ⟨Or.inl hχ, h4⟩
    refine ⟨β, Finset.mem_filter.mpr ⟨hβB, ?_⟩, hwβ⟩
    have h1' : σ₁ ≤ β := by rw [hwβ] at h1; simpa using h1
    have hne := hσ₁B β hβB
    rcases lt_or_eq_of_le h1' with h | h
    · exact h
    · exfalso
      rw [h, sub_self, abs_zero] at hne
      have hp : 0 < c₁ / (24 * L) := div_pos hc₁ (by linarith)
      linarith
  have hrect := hRS q χ hχ y hy0 σ₁ σ₀ T (B.filter (fun β => σ₁ < β)) hσ₁pos hσ₁lt1 hσ₀gt hT0
    hB₁ hzer hB₁z
  have hdec := perron_contour_decomposition hP χ y σ₁ σ₀ T _ hy1 hσ₀gt hT0.le hrect

  have hAnn : 0 ≤ (Real.log y + C₀) * (Real.exp 1 * y) :=
    mul_nonneg (by linarith) (mul_pos (Real.exp_pos 1) hy0).le
  have hI1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T := by
    refine Formalism.ZF.norm_integral_compl_le (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) _ T hAnn hT0 (fun t ht => ?_)
    show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
    rw [hσ₀e]
    exact perron_right_line_bound χ C₀ hR y T t hy1' hT0 ht

  have hHnn : 0 ≤ (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 := by
    have hCL : 0 ≤ C * L ^ 2 + 1 := by
      have := mul_nonneg hC (sq_nonneg L)
      linarith
    exact div_nonneg (mul_nonneg hCL (mul_pos (Real.exp_pos 1) hy0).le) (sq_nonneg T)
  have hH : ∀ v : ℝ, |v| = T → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3 := by
    intro v hv
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := σ₁) (b := σ₀) (f := fun x : ℝ => Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2) (fun x hx => by
        rw [Set.uIoc_of_le hσσ] at hx
        have hx' := perron_horizontal_segment_bound χ c₁ C B hBc hD y T x v σ₀ σ₁ hy1 hT hv hσ₁reg
          hx.1.le hx.2
        rw [hL, hyσ₀] at hx'
        exact hx')
    exact hb.trans (mul_le_mul_of_nonneg_left hσdiff hHnn)

  have hV : ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (f := fun u : ℝ => Fchi χ y ((σ₁ : ℂ) + u * I))
      (C := (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁)) (fun u hu => by
        rw [Set.uIoc_of_le (by linarith)] at hu
        have hu' : |u| ≤ T := abs_le.mpr ⟨hu.1.le, hu.2⟩
        have hb' := perron_left_line_bound χ c₁ C hc₁.le hC B hBc hD y T u σ₁ (c₁ / (24 * L))
          (c₁ / (4 * L)) hy0 hu' hσ₁reg hhalf (div_pos hc₁ (by linarith)) hgap
          (div_pos hc₁ (by linarith)) hσ₁B
        rw [hL, h1δ, h2ε] at hb'
        exact hb')
    have h2T : |T - -T| = 2 * T := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
    rw [h2T] at hb
    exact hb

  have hO : ‖∑ β ∈ B \ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (8 * L / c₁) := by
    refine norm_sum_le_of_card_le_one _ ((Finset.card_le_card Finset.sdiff_subset).trans hBc)
      (fun β : ℝ => (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))) _
      (mul_nonneg (Real.rpow_nonneg hy0.le _) (div_pos (by linarith) hc₁).le) (fun β hβ => ?_)
    rw [Finset.mem_sdiff] at hβ
    have hβσ : β ≤ σ₁ := by
      by_contra hc
      push_neg at hc
      exact hβ.2 (Finset.mem_filter.mpr ⟨hβ.1, hc⟩)
    have hreg := (hBz β hβ.1).2.1
    unfold InRegion at hreg
    simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hreg
    have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by nlinarith)
    have hlq : (1:ℝ) / 2 < Real.log ((q : ℝ) * 2) := by linarith
    have hlqne : Real.log ((q : ℝ) * 2) ≠ 0 := by linarith
    have hr : c₁ / Real.log ((q : ℝ) * 2) * Real.log ((q : ℝ) * 2) = c₁ := by field_simp
    have hrpos : 0 ≤ c₁ / Real.log ((q : ℝ) * 2) := div_nonneg hc₁.le (by linarith)
    have hrh : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by nlinarith
    have hβhalf : 1 / 2 ≤ β := by linarith
    have hom := real_zero_residue_term_bound y β σ₁ (c₁ / (4 * L)) hy1 hβhalf hβσ (div_pos hc₁ (by linarith)) hgap
    rw [h2ε] at hom
    exact hom

  have hmain : ‖Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hX := norm_nonneg (Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))))
    have h2pi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hXX := mul_le_mul_of_nonneg_right h2pi hX
    have hbot := hH (-T) (by rw [abs_neg]; exact hTabs)
    have htop := hH T hTabs
    linarith
  rw [← Finset.sum_sdiff (Finset.filter_subset (fun β => σ₁ < β) B)]
  calc ‖Schi χ y - negLD χ 1 * y + (∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) + ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖
        = ‖(Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))) + ∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hmain hO

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.IteratedDerivLseriesAlternatingNonneg
section
open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_lseries_at_two {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) : 1 ≤ LSeries a 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℂ).re : EReal) := by
    have e : ((2 : ℂ).re : EReal) = ((2 : ℝ) : EReal) := by norm_num
    rw [e]
    exact lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt
  have h1 : LSeries.term a 2 1 = 1 := by simp [LSeries.term, ha1]
  have hnn : ∀ j, 0 ≤ LSeries.term a 2 j := fun j => by simpa using LSeries.term_nonneg (ha0 j) 2
  rw [← h1]
  exact hs.le_tsum 1 (fun j _ => hnn j)

lemma iteratedDeriv_lseries_alternating_nonneg {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries a) 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have h := LSeries.iteratedDeriv_alternating (a := a) (fun m => ha0 m) (x := 2) hlt n
  simpa using h

theorem lseries_taylor_lower_bound {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {F G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries a s) (hFG : ∀ s : ℂ, s ≠ 1 → F s = G s + lam / (s - 1))
    {B : ℝ} (hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ B) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ)
    (hσ2 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖lam‖ * (2 - σ) ^ M / (1 - σ) - 4 * B * (3 / 4) ^ M ≤ (F σ).re := by
  set x : ℝ := 2 - σ with hxdef
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hx2 : x ≤ 9 / 8 := by rw [hxdef]; linarith
  have hFG' : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹ := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs
    rw [← hF s hs, hFG s hs1, div_eq_mul_inv]
  have hcoef := iteratedDeriv_lseries_at_two hG hFG'

  have hB0 : 0 ≤ B := by
    have hmem : (2 : ℂ) + ((3 / 2 : ℝ) : ℂ) ∈ Metric.sphere (2 : ℂ) (3 / 2) := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real]
      norm_num
    exact (norm_nonneg _).trans (hB _ hmem)

  set t : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n G 2 with htdef
  have hT : HasSum t (G σ) := Complex.hasSum_taylorSeries_of_entire hG 2 (σ : ℂ)
  have hsplit := hT.summable.sum_add_tsum_nat_add M
  rw [hT.tsum_eq] at hsplit
  set β : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries a) 2) with hβdef
  have hβ0 : ∀ n, 0 ≤ β n := by
    intro n
    refine mul_nonneg ?_ (iteratedDeriv_lseries_alternating_nonneg ha0 habs n)
    have : (0 : ℂ) ≤ (n ! : ℂ) := by exact_mod_cast (Nat.zero_le _)
    exact inv_nonneg.mpr this
  have hσx : (σ : ℂ) - 2 = -(x : ℂ) := by rw [hxdef]; push_cast; ring
  have ht : ∀ n, t n = (x : ℂ) ^ n * β n - lam * (x : ℂ) ^ n := by
    intro n
    have hg : iteratedDeriv n G 2 = iteratedDeriv n (LSeries a) 2 - lam * ((-1) ^ n * (n ! : ℂ)) := by
      rw [hcoef n]; ring
    have hpow : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; simp
    have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [htdef, hβdef, smul_eq_mul, hσx, hg, neg_pow (x : ℂ) n]
    have hQ : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hfac
    linear_combination (-(lam * (x : ℂ) ^ n * ((n ! : ℂ)⁻¹ * (n ! : ℂ)))) * hpow + (-(lam * (x : ℂ) ^ n)) * hQ

  have hfin : ∑ i ∈ Finset.range M, t i =
      ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i - lam * (((x : ℂ) ^ M - 1) / ((x : ℂ) - 1)) := by
    rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_sub_distrib, ← Finset.mul_sum, geom_sum_eq]
    intro h
    have : x = 1 := by exact_mod_cast h
    linarith
  have hpos : 1 ≤ ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i := by
    have hnn : ∀ i ∈ Finset.range M, 0 ≤ (x : ℂ) ^ i * β i := by
      intro i _
      refine mul_nonneg ?_ (hβ0 i)
      have : (0 : ℂ) ≤ (x : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ x)
      exact pow_nonneg this i
    have h0 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 0 < M))
    have hb0 : (x : ℂ) ^ 0 * β 0 = LSeries a 2 := by simp [hβdef]
    rw [hb0] at h0
    exact (one_le_lseries_at_two ha0 ha1 habs).trans h0

  have htail : ‖∑' i, t (i + M)‖ ≤ 4 * B * (3 / 4) ^ M := by
    have hg : HasSum (fun i : ℕ => B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i) (B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := tsum_of_norm_bounded hg (f := fun i => t (i + M)) (by
      intro i
      have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (i + M)
        (by norm_num : (0 : ℝ) < 3 / 2) hG.diffContOnCl hB
      have hnorm : ‖t (i + M)‖ = ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖ := by
        simp only [htdef, smul_eq_mul, norm_mul, norm_inv, norm_pow, hσx, norm_neg, Complex.norm_real,
          Complex.norm_natCast]
        rw [Real.norm_of_nonneg (by linarith)]
        ring
      rw [hnorm]
      have hfac : (0 : ℝ) < ((i + M) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hxp : 0 ≤ x ^ (i + M) := pow_nonneg (by linarith) _
      calc ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖
          ≤ ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * (((i + M) ! : ℝ) * B / (3 / 2) ^ (i + M)) := by
            gcongr
        _ = B * (x ^ (i + M) / (3 / 2) ^ (i + M)) := by field_simp
        _ = B * (x / (3 / 2)) ^ (i + M) := by rw [div_pow x (3 / 2 : ℝ)]
        _ ≤ B * (3 / 4) ^ (i + M) := by
            have hq : x / (3 / 2) ≤ 3 / 4 := by rw [div_le_iff₀ (by norm_num)]; linarith
            have hq0 : 0 ≤ x / (3 / 2) := by positivity
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) hB0
        _ = B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i := by rw [pow_add]; ring)
    calc ‖∑' i, t (i + M)‖ ≤ B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹ := hle
      _ = 4 * B * (3 / 4) ^ M := by norm_num; ring

  have hσ1' : (σ : ℂ) ≠ 1 := by
    intro h; have : σ = 1 := by exact_mod_cast h
    linarith
  have hkey : F σ = ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i
      - lam * (((x ^ M / (x - 1) : ℝ)) : ℂ) + ∑' i, t (i + M) := by
    rw [hFG σ hσ1', ← hsplit, hfin]
    have hx1' : (x : ℂ) - 1 ≠ 0 := by
      intro h; have : x = 1 := by
        have h' : ((x - 1 : ℝ) : ℂ) = 0 := by push_cast; exact h
        have := Complex.ofReal_eq_zero.mp h'; linarith
      linarith
    have hσc : (σ : ℂ) - 1 = -((x : ℂ) - 1) := by rw [hxdef]; push_cast; ring
    rw [hσc]
    push_cast
    field_simp
    ring
  have hre := congrArg Complex.re hkey
  rw [Complex.add_re, Complex.sub_re] at hre
  have h1 : 1 ≤ (∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i).re := by
    have := (Complex.le_def.mp hpos).1
    simpa using this
  have h2 : (lam * (((x ^ M / (x - 1) : ℝ)) : ℂ)).re ≤ ‖lam‖ * x ^ M / (x - 1) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
    · ring_nf; rfl
    · exact div_nonneg (pow_nonneg (by linarith) _) (by linarith)
  have h3 : -(4 * B * (3 / 4) ^ M) ≤ (∑' i, t (i + M)).re := by
    have := Complex.abs_re_le_norm (∑' i, t (i + M))
    have := neg_abs_le (∑' i, t (i + M)).re
    linarith
  have hx1s : x - 1 = 1 - σ := by rw [hxdef]; ring
  rw [hx1s] at h2 hre
  rw [hre]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

