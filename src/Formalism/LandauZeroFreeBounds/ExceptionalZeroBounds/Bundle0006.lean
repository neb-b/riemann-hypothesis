module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExcBoundOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma log_le_const_mul_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log (3 * x) ≤ K * x ^ δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h4 : Real.log 3 ≤ Real.log 3 * x ^ δ := by nlinarith
  have h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ := by ring
  rw [Real.log_mul (by norm_num) hx0.ne', h5]
  linarith

lemma rpow_neg_eq_inv_pow (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]

theorem exceptional_zero_bound_of : ExcBoundOf := by
  unfold ExcBoundOf ExcBound
  intro hS hL ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨c0, hc0, hS'⟩ := hS (ε / 3) hε3
  obtain ⟨C, hC⟩ := hL
  obtain ⟨K, hK, hKb⟩ := log_le_const_mul_rpow (ε / 3) hε3
  obtain ⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M := ⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  have hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2)) :=
    lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))
  refine ⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩
  intro q _ χ β hχ2 hχ1 hβ
  have hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K := min_le_left _ _
  have hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2) := min_le_right _ _
  generalize min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hu1 : 1 ≤ (q : ℝ) ^ (ε / 3) := Real.one_le_rpow hq1 hε3.le
  have hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹ := by
    have h := rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)
    simpa using h
  have hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹ := Real.rpow_neg hq0.le _
  have hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3) := hKb q hq1
  have hlog_pos : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hβ1 : β < 1 := by
    by_contra hge
    simp only [not_lt] at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ
  have hlow := hS' q χ hχ2 hχ1
  rw [hq3] at hlow
  rw [hqε]
  generalize (q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢
  have hu0 : 0 < u := by linarith
  by_cases hcase : β ≤ 1 - 1 / Real.log (3 * q)
  · have key : c * Real.log (3 * q) ≤ u ^ 3 := by
      have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
      calc c * Real.log (3 * q) ≤ (1 / K) * (K * u) :=
            mul_le_mul hcK hlogK hlog_pos.le (div_pos one_pos hK).le
        _ = u := by field_simp
        _ ≤ u ^ 3 := hu3
    have h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]
      exact key
    linarith
  · simp only [not_le] at hcase
    have hdiff := DirichletCharacter.differentiable_LFunction hχ1
    have hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 -
        (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤
        (C * Real.log (3 * q) ^ 2) * (1 - β) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1)
        (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩
      · intro t _
        exact ((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      · intro t ht
        exact hC q χ hχ1 t (by linarith [ht.1]) ht.2.le
    simp only [hβ, sub_zero, Complex.ofReal_one] at hmvt
    have h1β : 0 < 1 - β := by linarith
    have hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hlog_pos.le hlogK 2
    have hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2 :=
      mul_le_mul hCM hlog2 (sq_nonneg _) hM.le
    have hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β) :=
      le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))
    have hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β) := by
      have h := mul_le_mul_of_nonneg_right hmain hu0.le
      have e1 : c0 * u⁻¹ * u = c0 := by field_simp
      have e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β) := by ring
      linarith
    have hMKu : 0 < M * K ^ 2 * u ^ 3 := mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)
    have hfin : c * (u ^ 3)⁻¹ ≤ 1 - β := by
      calc c * (u ^ 3)⁻¹ ≤ c0 / (M * K ^ 2) * (u ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right hc2 (inv_nonneg.2 (pow_pos hu0 3).le)
        _ = c0 / (M * K ^ 2 * u ^ 3) := by field_simp
        _ ≤ 1 - β := by
          rw [div_le_iff₀ hMKu]
          linarith
    linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
section
open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma character_sum_range_modulus_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
    have h1 := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
  rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]

lemma norm_character_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hM : M < q
    · calc ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ ∑ n ∈ range M, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = M := by simp
        _ ≤ q := by exact_mod_cast hM.le
    · obtain ⟨M', rfl⟩ : ∃ M', M = q + M' := ⟨M - q, by omega⟩
      rw [character_sum_range_add_modulus χ hχ M']
      exact ih M' (by have := NeZero.pos q; omega)

lemma norm_character_sum_Icc_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have h1 : ∑ n ∈ range (M + 1), χ (n : ZMod q) =
      χ ((0 : ℕ) : ZMod q) + ∑ n ∈ Icc 1 M, χ (n : ZMod q) := by
    have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]
  have h2 : ∑ n ∈ Icc 1 M, χ (n : ZMod q) =
      ∑ n ∈ range (M + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q) := by
    rw [h1]; ring
  rw [h2]
  calc _ ≤ ‖∑ n ∈ range (M + 1), χ (n : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ q + 1 := add_le_add (norm_character_sum_range_le χ hχ _) (DirichletCharacter.norm_le_one χ _)

theorem lfunction_polynomial_growth : LGrowth := by
  refine ⟨9, ?_⟩
  intro q _ χ hχ s hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hσ : 0 < s.re := by linarith
  have hB := norm_character_sum_Icc_le χ hχ
  have hP := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) hB s hσ 1 le_rfl
  simp only [Nat.cast_one, Real.one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton] at hP
  have h1 : ‖χ (1 : ZMod q) * (1 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [one_cpow, mul_one]; exact DirichletCharacter.norm_le_one χ _
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ hσ]; nlinarith
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by
    have := norm_le_insert' (DirichletCharacter.LFunction χ s) (χ (1 : ZMod q) * (1 : ℂ) ^ (-s))
    linarith
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := hL
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + 2 * ‖s‖) := by gcongr
    _ ≤ 9 * q * (1 + ‖s‖) := by nlinarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
section
noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem landau_local3 : LandauLocal3 :=
  fun f z₀ r M hr hM hf hfz₀ hbound => exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogTwoLeLogAnalyticConductor
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_modulus_real (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)

lemma log_two_le_log_analytic_conductor (q : ℕ) [NeZero q] (t : ℝ) : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := one_le_modulus_real q
  have h2 := abs_nonneg t
  exact Real.log_le_log (by norm_num) (by nlinarith)

lemma log_analytic_conductor_ge_const (q : ℕ) [NeZero q] (t : ℝ) : 69 / 100 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h := Real.log_two_gt_d9
  have h2 := log_two_le_log_analytic_conductor q t
  linarith

lemma zero_free_region_mono_half {c₁ : ℝ} (hc : 0 < c₁) (q : ℕ) [NeZero q] (s : ℂ)
    (h : InRegion (c₁ / 2) q s) : InRegion c₁ q s := by
  unfold InRegion at h ⊢
  have hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_analytic_conductor q s.im)
  have h2 : c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le hL (by linarith)
  linarith

lemma re_ge_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  rw [Complex.sub_re] at h1
  have h2 := neg_abs_le (w.re - z₀.re)
  linarith

lemma norm_le_norm_add_of_mem_closedBall' {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have := norm_sub_norm_le w z₀
  linarith

lemma norm_disc_center_le (t : ℝ) : ‖(21 / 20 : ℂ) + t * I‖ ≤ 21 / 20 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(21 / 20 : ℂ)‖ = 21 / 20 := by
    rw [show (21 / 20 : ℂ) = ((21 / 20 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

lemma log_le_of_le_exp_log_conductor {A M L : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (hL : Real.log 2 ≤ L) (hX : 0 < Real.exp L)
    (hML : M ≤ 2 * A * Real.exp L) :
    Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * L := by
  have hA2 : 0 < 2 * A := by linarith
  have h1 : Real.log M ≤ Real.log (2 * A) + L := by
    have h := Real.log_le_log (by linarith) hML
    rwa [Real.log_mul hA2.ne' (Real.exp_pos L).ne', Real.log_exp] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 * A) ≤ Real.log (2 * A) / Real.log 2 * L := by
    have hq : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg hlA hl2.le
    calc Real.log (2 * A) = Real.log (2 * A) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ Real.log (2 * A) / Real.log 2 * L := mul_le_mul_of_nonneg_left hL hq
  rw [add_mul, one_mul]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronHorizontalSegmentBound
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem norm_perron_integrand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fchi χ y w‖ = ‖negLD χ w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  unfold Fchi
  rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]

theorem norm_sum_le_of_card_le_one (B : Finset ℝ) (hB : B.card ≤ 1) (f : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ β ∈ B, ‖f β‖ ≤ M) : ‖∑ β ∈ B, f β‖ ≤ M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with h | h
  · rw [Finset.card_eq_zero.mp h]; simpa using hM
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h
    simpa using hf b (Finset.mem_singleton_self b)

theorem perron_right_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fchi χ y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₀) * (Real.exp 1 * y) / t ^ 2 := by
  have hL0 : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  set w : ℂ := ((1 + 1 / L : ℝ) : ℂ) + t * I with hw
  have hwre : w.re = 1 + 1 / L := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  rw [norm_perron_integrand_eq χ y hy0 w, hwre]
  have hN : ‖negLD χ w‖ ≤ L + C₀ := by
    have hpos : 0 < 1 / L := by positivity
    have h1 := hR w (by rw [hwre]; linarith)
    rw [hwre] at h1
    simpa [one_div, inv_inv] using h1
  have hpow : y ^ (1 + 1 / L) = Real.exp 1 * y := by
    rw [Real.rpow_def_of_pos hy0, ← hL, mul_add, mul_one, mul_one_div_cancel hL0.ne',
      Real.exp_add, Real.exp_log hy0]
    ring
  have hw1 : |t| ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have h2 : (w - 1).im = t := by simp [hwim]
    rw [← h2]; exact Complex.abs_im_le_norm _
  rw [hpow]
  have htt : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have htt0 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hNn : 0 ≤ L + C₀ := le_trans (norm_nonneg _) hN
  have hey : 0 < Real.exp 1 * y := by positivity
  calc ‖negLD χ w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (L + C₀) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hN hey.le) (by positivity)
    _ ≤ (L + C₀) * (Real.exp 1 * y) / t ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hNn hey.le) htt0 htt

theorem log_conductor_pos_real (q : ℕ) [NeZero q] (u : ℝ) : 0 < Real.log ((q : ℝ) * (|u| + 2)) := by
  apply Real.log_pos
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg u]

theorem log_analytic_conductor_mono (q : ℕ) [NeZero q] (u T : ℝ) (hu : |u| ≤ T) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply Real.log_le_log
  · nlinarith [abs_nonneg u]
  · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

theorem perron_horizontal_segment_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T x v σ₀ σ₁ : ℝ) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁)
    (hx1 : σ₁ ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  set s : ℂ := (x : ℂ) + (v : ℂ) * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = v := by simp [hs]
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre, hv]; exact le_trans hσ₁ hx1
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β _ h
    have h1 := congrArg Complex.im h
    rw [hsim, Complex.ofReal_im] at h1
    rw [h1] at hv; simp at hv; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) 1 zero_le_one ?_
    intro β _
    rw [norm_div, norm_one]
    have h2 : (s - (β : ℂ)).im = v := by simp [hsim]
    have h1 : (1:ℝ) ≤ ‖s - (β : ℂ)‖ := by
      calc (1:ℝ) ≤ T := hT
        _ = |v| := hv.symm
        _ = |(s - (β : ℂ)).im| := by rw [h2]
        _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_im_le_norm _
    rw [div_le_one (by linarith)]; exact h1
  have hD' := hD s hreg hne
  rw [hsim, hv] at hD'
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    linarith
  rw [norm_perron_integrand_eq χ y hy0 s, hsre]
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := le_trans (norm_nonneg _) hN
  have hyx : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx2
  have hw1 : T ≤ ‖s‖ := by rw [← hv, ← hsim]; exact Complex.abs_im_le_norm s
  have hw2 : T ≤ ‖s - 1‖ := by
    have h4 : (s - 1).im = v := by simp [hsim]
    rw [← hv, ← h4]; exact Complex.abs_im_le_norm _
  have hden : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  calc ‖negLD χ s‖ * y ^ x / (‖s‖ * ‖s - 1‖)
      ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / (‖s‖ * ‖s - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul hN hyx (by positivity) hK) (by positivity)
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hK (Real.rpow_nonneg hy0.le _)) (by positivity) hden

theorem perron_left_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (hc₁ : 0 ≤ c₁) (hC : 0 ≤ C) (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T u σ₁ δ ε : ℝ) (hy : 0 < y) (hu : |u| ≤ T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁) (hhalf : 1 / 2 ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) (hδ : 0 < δ) (hδB : ∀ β ∈ B, δ ≤ |σ₁ - β|) :
    ‖Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) := by
  set s : ℂ := (σ₁ : ℂ) + (u : ℂ) * I with hs
  have hsre : s.re = σ₁ := by simp [hs]
  have hsim : s.im = u := by simp [hs]
  have hLu := log_conductor_pos_real q u
  have hmono := log_analytic_conductor_mono q u T hu
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre]
    refine le_trans ?_ hσ₁
    have h1 : (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ (c₁ / 2) / Real.log ((q : ℝ) * (|u| + 2)) :=
      div_le_div_of_nonneg_left (by linarith) hLu hmono
    linarith
  have hdist : ∀ β ∈ B, δ ≤ ‖s - (β : ℂ)‖ := by
    intro β hβ
    have h1 : (s - (β : ℂ)).re = σ₁ - β := by simp [hsre]
    calc δ ≤ |σ₁ - β| := hδB β hβ
      _ = |(s - (β : ℂ)).re| := by rw [h1]
      _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_re_le_norm _
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β hβ h
    have h1 := hdist β hβ
    rw [h, sub_self, norm_zero] at h1; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 / δ := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) (1 / δ) (by positivity) ?_
    intro β hβ
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ (hdist β hβ)
  have hD' := hD s hreg hne
  rw [hsim] at hD'
  have hlogsq : Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
    pow_le_pow_left₀ hLu.le hmono 2
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    have h4 : C * Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq hC
    linarith
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := le_trans (norm_nonneg _) hN
  rw [norm_perron_integrand_eq χ y hy s, hsre]
  have hw1 : 1 / 2 ≤ ‖s‖ := by
    calc (1:ℝ) / 2 ≤ σ₁ := hhalf
      _ ≤ |σ₁| := le_abs_self _
      _ = |s.re| := by rw [hsre]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hw2 : ε ≤ ‖s - 1‖ := by
    have h5 : (s - 1).re = σ₁ - 1 := by simp [hsre]
    calc ε ≤ 1 - σ₁ := hgap
      _ ≤ |σ₁ - 1| := by rw [abs_sub_comm]; exact le_abs_self _
      _ = |(s - 1).re| := by rw [h5]
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hden : ε / 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  have hden0 : 0 < ‖s‖ * ‖s - 1‖ := by linarith
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ hden0]
  calc ‖negLD χ s‖ * y ^ σ₁ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ :=
        mul_le_mul_of_nonneg_right hN hyp.le
    _ = (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (ε / 2) := by
        rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (‖s‖ * ‖s - 1‖) :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg hK hyp.le) (by positivity))

theorem real_zero_residue_term_bound (y β σ₁ ε : ℝ) (hy : 1 ≤ y) (hβ : 1 / 2 ≤ β) (hβσ : β ≤ σ₁) (hε : 0 < ε)
    (hgap : ε ≤ 1 - σ₁) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (2 / ε) := by
  have hy0 : 0 < y := by linarith
  have hβ1 : β < 1 := by linarith
  have hnum : ‖(y : ℂ) ^ (β : ℂ)‖ = y ^ β := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp
  have hden : ‖(β : ℂ) * ((β : ℂ) - 1)‖ = β * (1 - β) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_neg (by linarith)]
    ring
  rw [norm_div, hnum, hden]
  have hyb : y ^ β ≤ y ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hy hβσ
  have hd : ε / 2 ≤ β * (1 - β) := by
    nlinarith [mul_le_mul_of_nonneg_right hβ (by linarith : (0:ℝ) ≤ 1 - β)]
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy0 _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ (by linarith)]
  calc y ^ β ≤ y ^ σ₁ := hyb
    _ = y ^ σ₁ * (2 / ε) * (ε / 2) := by rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ y ^ σ₁ * (2 / ε) * (β * (1 - β)) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hyp.le (by positivity))

end Formalism.ZeroFreeDirichlet
end
end

