module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0005

@[expose] public section

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.GzPNTOf
section
open Complex

noncomputable section

namespace Formalism.ZF

private theorem abs_zetaPrimeSumError_le_of_sqrt_log_lt (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 2 ≤ y)
    (hs : Real.sqrt (Real.log y) < 8 / c) :
    |Formalism.Gz y| ≤
      ((Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1) * y *
        Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hsq : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hlogL : Real.log y ≤ (8 / c) ^ 2 := by
    calc Real.log y = Real.sqrt (Real.log y) ^ 2 := (Real.sq_sqrt hlog).symm
      _ ≤ (8 / c) ^ 2 := pow_le_pow_left₀ hsq hs.le 2
  have hyL : y ≤ Real.exp ((8 / c) ^ 2) := by
    calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
      _ ≤ Real.exp ((8 / c) ^ 2) := Real.exp_le_exp.mpr hlogL
  have hinner : y * Real.log y + Real.log y + 2 ≤
      Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 := by
    have := mul_le_mul hyL hlogL hlog (Real.exp_pos _).le
    linarith
  have hcs : (c / 8) * Real.sqrt (Real.log y) ≤ 1 := by
    calc (c / 8) * Real.sqrt (Real.log y) ≤ (c / 8) * (8 / c) :=
          mul_le_mul_of_nonneg_left hs.le (by positivity)
      _ = 1 := by field_simp
  have hexp : Real.exp (-1) ≤ Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    Real.exp_le_exp.mpr (by linarith)
  set M : ℝ := Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMe : M = M * Real.exp 1 * Real.exp (-1) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  calc |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) :=
        abs_zetaPrimeSumError_le_of_one_le y (by linarith)
    _ ≤ y * M := mul_le_mul_of_nonneg_left hinner hy0.le
    _ = y * (M * Real.exp 1 * Real.exp (-1)) := by rw [← hMe]
    _ ≤ y * (M * Real.exp 1 * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by
        apply mul_le_mul_of_nonneg_left _ hy0.le
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = M * Real.exp 1 * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

theorem zetaPrimeSumErrorBoundOfBounds : GzPNTOf := by
  intro hZF hLD hRH hP hRS
  obtain ⟨c₀, hc₀, hZ⟩ := hZF
  obtain ⟨c₁, C₁, hc₁, hD⟩ := hLD
  obtain ⟨C₂, hC₂, hR⟩ := hRH
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max C₁ 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hDdef ▸ le_max_right _ _
  have hD' : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ D * Real.log (|s.im| + 2) ^ 2 := by
    intro s hs hre
    exact (hD s hs hre).trans
      (mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _) (sq_nonneg _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (min c₀ c₁) (1 / 2) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ lt_min (lt_min hc₀ hc₁) (by norm_num)
  have hc2 : c ≤ 1 / 2 := hcdef ▸ min_le_right _ _
  have hcc₀ : c ≤ c₀ := hcdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := hcdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (D + 1) +
      4 * (D + 1)) * (6 * (8 / c) ^ 3) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B =
      (Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1 := ⟨_, rfl⟩
  refine ⟨c / 8, max A B, div_pos hc (by norm_num), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  have hyE : 0 ≤ y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    mul_nonneg hy0 (Real.exp_pos _).le
  have h8c : 16 ≤ 8 / c := by
    rw [le_div_iff₀ hc]; linarith
  by_cases hs : 8 / c ≤ Real.sqrt (Real.log y)
  · have hs1 : 1 ≤ Real.sqrt (Real.log y) := by linarith
    have h := abs_zetaPrimeSumError_le_of_large c₀ c₁ D C₂ hD0 hC₂ hZ hD' hR hP hRS
      c hc hc2 hcc₀ hcc₁ y hy hs hs1
    rw [← hA] at h
    calc |Formalism.Gz y| ≤ A * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = A * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
  · rw [not_le] at hs
    have h := abs_zetaPrimeSumError_le_of_sqrt_log_lt c hc y hy hs
    rw [← hB] at h
    calc |Formalism.Gz y| ≤ B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrMid
section
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_mid {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by
  set T := |t| with hTdef
  set L := Real.log (T + 2) with hLdef
  have hLpos : 0 < L := by linarith
  have hT0 : 0 ≤ T := abs_nonneg t
  have hLX : L ≤ T + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith)
    linarith
  have hT3 : 3 ≤ T := by linarith
  set u := 1 / L with hudef
  have hu : 0 < u := by positivity
  have hu24 : u ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) hL
  have hLu : L * u = 1 := by rw [hudef]; field_simp
  set σ₀ := 1 + u with hσ₀def
  have hσ₀1 : 1 < σ₀ := by linarith
  have hσ₀2 : σ₀ ≤ 2 := by linarith
  have hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2) := by
    have e : 2 / (σ₀ - 1) = 2 * L := by
      rw [show σ₀ - 1 = u by ring, hudef, div_div_eq_mul_div, div_one]
    rw [e]; linarith
  set z₀ : ℂ := (σ₀ : ℂ) + t * I with hz₀
  have hz0re : z₀.re = σ₀ := by simp [z₀]
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; exact hσ₀1)
  have hM := zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith)
  have hM1 : 1 ≤ (T + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨Z, m, hZ, hm, hsum, hder⟩ :=
    hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num) hM1 (zfo_diff_ball hT3) hz0 hM
  have hlogM : Real.log ((T + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogM] at hsum hder
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsz : s - z₀ = ((σ - σ₀ : ℝ) : ℂ) := by
    simp only [s, z₀, Complex.ofReal_sub]; ring
  have hs_mem : s ∈ closedBall z₀ (1 / 2 / 6) := by
    rw [mem_closedBall, dist_eq_norm, hsz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at hTdef; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; exact ht0 this
  have hc4 : (c₀ / 4) / L ≤ c₀ / L := div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hs_ne : riemannZeta s ≠ 0 := by
    apply hZ0 s hs1
    rw [hsre, hsim]; linarith
  have hD := hder s hs_mem hs_ne

  set δ := (c₀ / 4) / L with hδdef
  have hδ : 0 < δ := by positivity
  have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ := by
    intro ρ hρ
    obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
    rw [mem_closedBall, dist_eq_norm] at hρb
    have him : |ρ.im - t| ≤ 1 / 6 := by
      have h1 : (ρ - z₀).im = ρ.im - t := by simp [z₀]
      rw [← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)
    have hρim : |ρ.im| ≤ T + 1 / 6 := by
      have := abs_sub_abs_le_abs_sub ρ.im t; linarith
    have hρim' : T - 1 / 6 ≤ |ρ.im| := by
      have := abs_sub_abs_le_abs_sub t ρ.im; rw [abs_sub_comm] at this; linarith
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at hρim'; linarith
    have hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2) := by
      by_contra hc; exact hZ0 ρ hρ1 (not_lt.mp hc) hρ0
    have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      have e : 2 * L = Real.log ((T + 2) ^ 2) := by rw [Real.log_pow]; push_cast; ring
      rw [e]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hlogρpos : 0 < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have h2 : c₀ / (2 * L) ≤ c₀ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₀.le hlogρpos hlogρ
    have h3 : c₀ / (2 * L) = 2 * δ := by rw [hδdef]; field_simp; ring
    have hsρ : δ < (s - ρ).re := by rw [Complex.sub_re, hsre]; linarith
    have hn : δ < ‖s - ρ‖ := lt_of_lt_of_le hsρ (Complex.re_le_norm _)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le
  have hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2 := by
    have h1 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have h2 : ∑ ρ ∈ Z, (m ρ : ℝ) / δ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
      rw [← Finset.sum_div]; push_cast; rfl
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2pos : 0 < Real.log 2 := by linarith
    have h3 : 10 * L / Real.log 2 ≤ 15 * L := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have h4 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ ≤ 15 * L / δ :=
      div_le_div_of_nonneg_right (hsum.trans h3) hδ.le
    have h5 : 15 * L / δ = (60 / c₀) * L ^ 2 := by rw [hδdef]; field_simp; ring
    linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := ldr_inv_sub_one_le (by rw [hsim]; linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1) := by ring
  have hD' : (72 : ℝ) * (10 * L) / (1 / 2) = 1440 * L := by ring
  rw [hD'] at hD
  have htot : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 1440 * L + (60 / c₀) * L ^ 2 + 1 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hLL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf
section
open Complex

noncomputable section

namespace Formalism.ZF

theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf := by
  intro h341 hLDR hG hI hSH hLL
  obtain ⟨t₀, -, ht₀⟩ := zfo_large h341 hLDR hG hI hLL
  obtain ⟨c₂, hc₂, hsmall⟩ := hSH t₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (c₂ * Real.log 2), lt_min (by norm_num) (mul_pos hc₂ hlog2), ?_⟩
  intro s hs1 hre
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hL
  rcases le_or_gt |s.im| t₀ with hT | hT
  · apply hsmall s hT _ hs1
    have hc : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₂ := by
      rw [div_le_iff₀ hLpos]
      calc min (1 / 200000) (c₂ * Real.log 2) ≤ c₂ * Real.log 2 := min_le_right _ _
        _ ≤ c₂ * Real.log (|s.im| + 2) := mul_le_mul_of_nonneg_left hL hc₂.le
    linarith
  · intro hz
    have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hβ := ht₀ s.re s.im hT.le (by rw [← hs]; exact hz)
    have h2 : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ (1 / 200000) / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith

end Formalism.ZF
end
end

