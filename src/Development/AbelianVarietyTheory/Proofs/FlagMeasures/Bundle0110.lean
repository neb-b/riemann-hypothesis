module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsGapsExceed
section
open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem gaps_exceed :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k →
      C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧
      C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧
      C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  intro eps CD heps _heps' hCD C hC
  refine ⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩
  intro x hx m f k lrd Del h r hkr hrk
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC' : C ^ (100 / eps) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx16 : (16 : ℝ) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4 := by
      gcongr
      exact h.m_lo
    have h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
    linarith
  have hf : x ≤ f := le_trans hm4 h.mf
  have hk : x ≤ k := le_trans hf h.fk
  have hr : x ≤ r := le_trans hk hkr
  have hf1 : 1 ≤ f := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le
  have hL' : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx1 (by positivity)
  have hm10 : m ^ 10 ≤ f ^ 3 := by
    have h1 : m ^ 10 ≤ m ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
    have h2 : m ^ 12 = (m ^ 4) ^ 3 := by ring
    have h3 : (m ^ 4) ^ 3 ≤ f ^ 3 := by gcongr; exact h.mf
    linarith
  have hf3 : f ≤ f ^ 3 := by
    have := pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this
  have hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3 := by
    have h1 : C * k * m ^ 4 ≤ C * k * f ^ 3 := by
      have : m ^ 4 ≤ f ^ 3 := le_trans h.mf hf3
      gcongr
    have h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3 := by
      gcongr
    nlinarith
  have hSpos : 0 < C * k * m ^ 4 + r * m ^ 10 := by positivity

  have hy1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := one_le_mul_of_one_le_of_one_le hk1 hf1
    exact one_le_mul_of_one_le_of_one_le this hL
  have hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hCD
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith [h.Del_lo]
  have hDelpos : 0 < Del := by
    have : 0 < (k * f * x ^ eps) ^ (3 : ℕ) := by positivity
    linarith
  have hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del := by
    have hkf3 : 0 < k * f ^ 3 := by positivity
    have hk2 : C + 2 < 4 * k ^ 2 := by nlinarith
    have e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3) := by nlinarith
    have e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ) := by
      have hkf : k * f ≤ k * f * x ^ eps := le_mul_of_one_le_right (by positivity) hL
      have : (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3 := by gcongr
      nlinarith
    linarith

  set t := x ^ (eps / 2) with ht
  have ht16 : 16 ≤ t := by
    have h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (by positivity) hx16 (by positivity)
    have h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 / eps * (eps / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hxe : x ^ eps = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
  have hDelE : Del ≤ Real.exp t := by
    have := h.Del_hi
    rw [Real.log_le_iff_le_exp hDelpos] at this
    exact this
  have hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) := by
    rw [Real.lt_sqrt hSpos.le]
    have e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2 := by
      have : C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t := by linarith
      gcongr
    have e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      rw [show 2 * t = t + t by ring, Real.exp_add]; ring
    have e3 : Real.log 16 + 2 * t ≤ x ^ eps := by
      have : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [hxe]; nlinarith
    have e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps := by
      unfold bx; exact Real.exp_le_exp.mpr e3
    linarith

  have hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hf35 : f ^ 3 ≤ f ^ 5 := pow_le_pow_right₀ hf1 (by norm_num)
    have e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5 := by
      have : (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5 := by gcongr
      linarith
    have hx18 : x ≤ x ^ 18 := by
      have := pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this
    have hr18 : x ^ 18 ≤ r ^ 18 := by gcongr
    have e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5) := by
      have hp : 0 < r * f ^ 5 := by positivity
      have hC18 : C + 2 < r ^ 18 := by
        have hx2 : x ^ 2 ≤ x ^ 18 := pow_le_pow_right₀ hx1 (by norm_num)
        have : x < x ^ 2 := by nlinarith
        linarith
      have := mul_lt_mul_of_pos_right hC18 hp
      calc (C + 2) * r * f ^ 5 = (C + 2) * (r * f ^ 5) := by ring
        _ < r ^ 18 * (r * f ^ 5) := this
    have e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5 := by ring
    have e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
      have hp : 0 ≤ r ^ 19 * f ^ 5 := by positivity
      have h1 : 1 ≤ x ^ (eps / 100) * x ^ eps := one_le_mul_of_one_le_of_one_le hL' hL
      have := mul_le_mul_of_nonneg_right h1 hp
      calc r ^ 19 * f ^ 5 = 1 * (r ^ 19 * f ^ 5) := by ring
        _ ≤ (x ^ (eps / 100) * x ^ eps) * (r ^ 19 * f ^ 5) := this
        _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
    linarith

  have hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hCx : C ≤ x ^ (eps / 100) := by
      have h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100) :=
        Real.rpow_le_rpow (by positivity) hxC' (by positivity)
      have h2 : (C ^ (100 / eps)) ^ (eps / 100) = C := by
        rw [← Real.rpow_mul hC.le]
        have : 100 / eps * (eps / 100) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps := by positivity
    have := mul_le_mul_of_nonneg_right hCx hp
    calc C * r ^ 19 * f ^ 5 * x ^ eps = C * (r ^ 19 * f ^ 5 * x ^ eps) := by ring
      _ ≤ x ^ (eps / 100) * (r ^ 19 * f ^ 5 * x ^ eps) := this
      _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
  exact ⟨hc1, hc2, hc3, hc4⟩

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRootDiscriminantClauses
section
open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem rankNums_rootDisc :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del →
        C * (m * (lrd - Real.log 2)) ≤ k ∧ C * (m ^ 3 * x ^ eps * lrd) ≤ k * Real.log k ^ 2 ∧
          lrd ≤ x ^ eps / C := by
  intro eps CD heps _ _ C hC
  set M : ℝ := max C 3 with hMdef
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMC : C ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  refine ⟨max (max 1 C) (M ^ (2 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxM : M ^ (2 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set X : ℝ := x ^ (eps / 2) with hXdef
  have hXM : M ≤ X := by
    have h1 : (M ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hxM (by linarith)
    rw [← Real.rpow_mul hM0] at h1
    have h2 : 2 / eps * (eps / 2) = 1 := by field_simp
    rw [h2, Real.rpow_one] at h1
    exact h1
  have hYX : x ^ eps = X * X := by
    rw [hXdef, ← Real.rpow_add hx0]; ring_nf
  have hX3 : 3 ≤ X := le_trans hM3 hXM
  have hXC : C ≤ X := le_trans hMC hXM
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    calc x = (x ^ ((1 : ℝ) / 4)) ^ 4 := h1.symm
      _ ≤ m ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) h.m_lo 4
  have hf : x ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := le_trans hx1 hf
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm3 : 1 ≤ m ^ 3 := one_le_pow₀ hm1
  have hm4' : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hk : X * (m ^ 5 * f * (X * X)) ≤ k := by
    have := h.k_lo; rw [hYX] at this; exact this
  have hlrd : lrd ≤ X := h.lrd_hi
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlrd0 : 0 ≤ lrd := le_trans hlog2 h.lrd_lo
  have hX0 : 0 ≤ X := by linarith
  have hXX : X ≤ X * X := by nlinarith

  have hA : C ≤ m ^ 4 * f * (X * X) := by
    have h1 : 1 ≤ m ^ 4 * f := by nlinarith
    calc C ≤ X * X := le_trans hXC hXX
      _ = 1 * (X * X) := by ring
      _ ≤ m ^ 4 * f * (X * X) := mul_le_mul_of_nonneg_right h1 (by positivity)

  have hB : C ≤ m ^ 2 * f := by
    calc C ≤ x := hxC
      _ ≤ f := hf
      _ = 1 * f := by ring
      _ ≤ m ^ 2 * f := mul_le_mul_of_nonneg_right hm2 (by linarith)
  have hkX : X ≤ k := by
    have h1 : 1 ≤ m ^ 5 * f * (X * X) := by
      have : 1 ≤ m ^ 5 := one_le_pow₀ hm1
      have : 1 ≤ X * X := by nlinarith
      have : 1 ≤ m ^ 5 * f := by nlinarith
      nlinarith
    nlinarith
  have hk0 : 0 < k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc C * (m * (lrd - Real.log 2)) ≤ C * (m * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left _ hm0
          linarith
      _ = (m * X) * C := by ring
      _ ≤ (m * X) * (m ^ 4 * f * (X * X)) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
  · have hlogk : 1 ≤ Real.log k := by
      rw [Real.le_log_iff_exp_le hk0]
      have := Real.exp_one_lt_d9
      linarith
    have hl2 : 1 ≤ Real.log k ^ 2 := one_le_pow₀ hlogk
    rw [hYX]
    calc C * (m ^ 3 * (X * X) * lrd) ≤ C * (m ^ 3 * (X * X) * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left hlrd (by positivity)
      _ = (m ^ 3 * (X * X) * X) * C := by ring
      _ ≤ (m ^ 3 * (X * X) * X) * (m ^ 2 * f) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
      _ = k * 1 := by ring
      _ ≤ k * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hl2 hk0.le
  · rw [hYX, le_div_iff₀ hC]
    calc lrd * C ≤ X * C := mul_le_mul_of_nonneg_right hlrd hC.le
      _ ≤ X * X := mul_le_mul_of_nonneg_left hXC hX0

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisons
section
open GlobalTheory.Diag.PG Filter

noncomputable section

namespace GlobalTheory.Diag.PG.SqrtBound

theorem poly_ineq {t K a : ℝ} (ht2 : 2 ≤ t) (htK : K ≤ t) (ha : a ≤ K) : a * t + t ^ 2 ≤ t ^ 4 / 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hat : a * t ≤ t * t := mul_le_mul_of_nonneg_right (ha.trans htK) ht0
  have h4 : 4 ≤ t ^ 2 := by nlinarith
  nlinarith

theorem scale_facts {eps x : ℝ} (heps : 0 < eps) (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ (eps / 4) / eps ∧ x ^ (eps / 2) = (x ^ (eps / 4)) ^ 2 ∧
      x ^ eps = (x ^ (eps / 4)) ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.log_le_rpow_div hx0 (by positivity : 0 < eps / 4)
    calc Real.log x ≤ x ^ (eps / 4) / (eps / 4) := h
      _ = 4 * x ^ (eps / 4) / eps := by field_simp
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf

theorem exp_bound {eps A x K : ℝ} (heps : 0 < eps) (hA : 0 < A) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : |Real.log A| + 40 / eps ≤ K) :
    A * x ^ 10 * Real.exp (x ^ (eps / 2)) ≤ Real.exp (x ^ eps / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hlog, h2, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have hp := poly_ineq (a := |Real.log A| + 40 / eps) ht2 htK hK
  have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
  have h3 : |Real.log A| ≤ |Real.log A| * t := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have h5 : 10 * Real.log x ≤ 40 / eps * t := by
    calc 10 * Real.log x ≤ 10 * (4 * t / eps) := by linarith
      _ = 40 / eps * t := by ring
  have key : Real.log A + 10 * Real.log x + t ^ 2 ≤ t ^ 4 / 2 := by nlinarith
  have e10 : Real.exp (10 * Real.log x) = x ^ 10 := by
    rw [show (10 : ℝ) * Real.log x = Real.log (x ^ 10) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (by positivity)
  calc A * x ^ 10 * Real.exp (x ^ (eps / 2))
        = Real.exp (Real.log A + 10 * Real.log x + x ^ (eps / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hA, e10]
    _ ≤ Real.exp (x ^ eps / 2) := Real.exp_le_exp.2 (by rw [h2, h4]; linarith)

theorem log_bound {eps C x K : ℝ} (heps : 0 < eps) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : 20 * C / eps ≤ K) :
    Real.log x * (5 * C) ≤ x ^ eps / 2 := by
  obtain ⟨hlog, -, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have ht0 : 0 ≤ t := by linarith
  have hp := poly_ineq (a := 20 * C / eps) ht2 htK hK
  have hat : 0 ≤ 20 * C / eps * t := by positivity
  have h1 : Real.log x * (5 * C) ≤ 4 * t / eps * (5 * C) :=
    mul_le_mul_of_nonneg_right hlog (by positivity)
  have h2 : 4 * t / eps * (5 * C) = 20 * C / eps * t := by ring
  rw [h4]
  nlinarith

theorem rankNums_sizes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧
      max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧
      Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧
      (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  intro eps CD heps _ hCD C hC
  set K0 := max (max 2 (|Real.log C| + 40 / eps)) (max (|Real.log 12| + 40 / eps) (20 * C / eps)) with hK0
  have hK0pos : 0 ≤ K0 := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max 1 (K0 ^ (4 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have htK0 : K0 ≤ x ^ (eps / 4) := by
    have h1 : K0 ^ (4 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ eps / 4)
    rwa [← Real.rpow_mul hK0pos, show 4 / eps * (eps / 4) = (1 : ℝ) by field_simp, Real.rpow_one] at h2
  have ht2 : 2 ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htK0
  have htA : |Real.log C| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htK0
  have ht12 : |Real.log 12| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) htK0
  have htC : 20 * C / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) htK0

  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : m ≤ m ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 3]
  have hf1 : 1 ≤ f := le_trans (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 4]) h.mf
  have hk1 : 1 ≤ k := le_trans hf1 h.fk
  have hk5 : k ≤ x ^ 5 := by
    have := h.k_hi
    rwa [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hm5 : m ≤ x ^ 5 := le_trans (le_trans hm4 (le_trans h.mf h.fk)) hk5
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le

  have hB1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := by nlinarith
    nlinarith
  have hDel1 : 1 ≤ Del := le_trans (Real.one_le_rpow hB1 (by linarith)) h.Del_lo
  have hDelE : Del ≤ Real.exp (x ^ (eps / 2)) :=
    (Real.log_le_iff_le_exp (by linarith)).1 h.Del_hi

  have hsq : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
    rw [Real.sqrt_eq_rpow, bx, ← Real.exp_mul]; ring_nf
  have hE0 : 0 ≤ Real.exp (x ^ (eps / 2)) := (Real.exp_pos _).le
  have hx10 : m * k ≤ x ^ 10 := by
    have : x ^ 10 = x ^ 5 * x ^ 5 := by ring
    rw [this]; exact mul_le_mul hm5 hk5 (by linarith) (by positivity)
  have hb1 : 1 ≤ bx x eps := Real.one_le_exp (by positivity)
  refine ⟨hDel1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsq]
    calc C * (m * k * Del) ≤ C * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          rw [mul_assoc C]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hx10 hDelE (by linarith) (by positivity)) hC.le
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps hC hx1 ht2 htA le_rfl
  · rw [hsq]
    refine max_le ?_ ?_
    · have hk0 : 0 < k := by linarith
      rw [Real.rpow_def_of_pos hk0]
      refine Real.exp_le_exp.2 (le_trans ?_ (log_bound heps hC.le hx1 ht2 htC le_rfl))
      have hlk : Real.log k ≤ 5 * Real.log x := by
        have h5 := Real.log_le_log hk0 hk5
        rw [Real.log_pow] at h5; push_cast at h5; linarith
      nlinarith
    · rw [bx, ← Real.exp_mul]
      exact Real.exp_le_exp.2 (by nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [hsq]
    calc 12 * k * Del ≤ 12 * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          have hk10 : k ≤ x ^ 10 := le_trans hk5 (pow_le_pow_right₀ hx1 (by norm_num))
          rw [mul_assoc, mul_assoc (12 : ℝ)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hk10 hDelE (by linarith) (by positivity)) (by norm_num)
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps (by norm_num) hx1 ht2 ht12 le_rfl
  · rw [hsq, bx, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [show bx x eps ^ 2 = bx x eps ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  · intro hCC
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hCC) h.Del_lo

end GlobalTheory.Diag.PG.SqrtBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantPosDefFormEqSmulInnerOfIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem exists_endomorphism_representing_sesquilinear_form
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : ∃ A : W →ₗ[ℂ] W, ∀ x y, B x y = ⟪x, A y⟫_ℂ := by
  classical
  let e := stdOrthonormalBasis ℂ W
  refine ⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩
  conv_lhs => rw [← e.sum_repr' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem invariant_posDef_form_eq_smul_inner_of_irreducible :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  intro W _ _ _ I π B hiso hirr hinv hherm hpos
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩
  obtain ⟨A, hA⟩ := exists_endomorphism_representing_sesquilinear_form W B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A v = μ • v := hv.apply_eq_smul
  have hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ := fun i x y =>
    (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y
  have hsurj : ∀ i, Function.Surjective (π i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1
      (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective
  let S : Submodule ℂ W :=
    { carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ}
      add_mem' := fun {a b} ha hb x => by
        rw [map_add (f := _), inner_add_right, ha x, hb x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by
        rw [map_smul, inner_smul_right, ha x, smul_eq_mul]; ring }
  have hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ := fun y => Iff.rfl
  have hvS : v ∈ S := by
    rw [hS]; intro x
    rw [hA, hAv, inner_smul_right]
  have hstab : ∀ i, ∀ y ∈ S, π i y ∈ S := by
    intro i y hy
    rw [hS] at hy ⊢
    intro x
    obtain ⟨x', rfl⟩ := hsurj i x
    rw [hinv, hinner, hy]
  have htop : S = ⊤ := by
    rcases hirr S hstab with h | h
    · rw [h] at hvS
      exact absurd ((Submodule.mem_bot ℂ).1 hvS) hv0
    · exact h
  have hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ := fun x y =>
    (hS y).1 (htop ▸ Submodule.mem_top) x
  have hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, inner_self_eq_norm_sq_to_K]; simp
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have him : μ.im = 0 := by
    have h1 := congrArg Complex.im (hherm v v)
    rw [hvv] at h1
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add] at h1
    have h2 : μ.im * ‖v‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right hn.ne'
  have hre : 0 < μ.re := by
    have h1 := hpos v hv0
    rw [hvv] at h1
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1
    exact (mul_pos_iff_of_pos_right hn).1 h1
  refine ⟨μ.re, hre, fun _ x y => ?_⟩
  have : (μ.re : ℂ) = μ := Complex.ext rfl (by simp [him])
  rw [this, hall]

end GlobalTheory
end

