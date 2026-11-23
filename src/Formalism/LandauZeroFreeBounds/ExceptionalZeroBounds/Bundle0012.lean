module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0009
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0010
public import Formalism.ZeroFreeRegion.LogDerivRegion

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem lfunction_one_upper_bound : LFunctionOneUpperBound := by
  refine ⟨38 * Real.exp (3 / 2), ?_⟩
  intro q _ χ hχ
  have hq : 3 ≤ q := three_le_modulus_of_ne_one χ hχ
  have hlog : 2 ≤ Real.log (3 * (q : ℝ)) := two_le_log_three_mul q hq
  have hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ))) := div_pos (by norm_num) (by linarith)
  exact lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith)
    (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivRegionChiOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem log_deriv_in_zero_free_region : LogDerivRegionChiOf := by
  intro hLL hG hInv hR c₁ hc₁ hc₁'
  obtain ⟨C, hC⟩ := hG
  obtain ⟨C₀, hC₀, hR⟩ := hR
  set A : ℝ := 21 * (|C| + 1) with hA
  have hA1 : 21 ≤ A := by have := abs_nonneg C; linarith
  set K₁ : ℝ := Real.log (2 * A) / Real.log 2 + 1 with hK₁
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₁0 : 1 ≤ K₁ := by
    have : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
    linarith
  refine ⟨2880 / 11 * K₁ + 3 * K₁ / (c₁ * Real.log 2) + 480 / 11 + 4 * (20 + C₀), ?_⟩
  intro q _ χ B hχ hB s hs hsB
  obtain ⟨hBcard, hBmem, hBall⟩ := hB
  have hq := one_le_modulus_real q
  set L := Real.log ((q : ℝ) * (|s.im| + 2)) with hLdef
  have hL69 : 69 / 100 ≤ L := log_analytic_conductor_ge_const q s.im
  have hL : 1 / 2 ≤ L := by linarith
  have hLsq : 1 ≤ 4 * L ^ 2 := by nlinarith
  have hLsq' : L ≤ 2 * L ^ 2 := by nlinarith
  have hT1 : 0 ≤ 2880 / 11 * K₁ := by positivity
  have hT2 : 0 ≤ 3 * K₁ / (c₁ * Real.log 2) := by positivity
  have hβlt : ∀ β ∈ B, β < 1 := by
    intro β hβ
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using le_of_not_gt h)
      (hBmem β hβ).2.2.1
  have hσlow : 1 - c₁ / 2 / L ≤ s.re := hs
  by_cases hσ : 11 / 10 ≤ s.re
  ·
    have h1 : ‖negLD χ s‖ ≤ 10 + C₀ := by
      have := hR q χ s (by linarith)
      have : 1 / (s.re - 1) ≤ 10 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h2 : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 10 := by
      calc ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ ∑ β ∈ B, ‖1 / (s - (β : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ β ∈ B, (10 : ℝ) := by
          apply Finset.sum_le_sum
          intro β hβ
          have hb := hβlt β hβ
          have hre : (s - (β : ℂ)).re = s.re - β := by simp
          have hn : 1 / 10 ≤ ‖s - (β : ℂ)‖ := by
            have := Complex.re_le_norm (s - (β : ℂ))
            linarith
          rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
          linarith
        _ = B.card * 10 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * 10 := by gcongr; exact_mod_cast hBcard
        _ = 10 := by ring
    have h3 : 0 ≤ (2880 / 11 * K₁ + 3 * K₁ / (c₁ * Real.log 2) + 480 / 11) * L ^ 2 := by positivity
    calc ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖
        ≤ ‖negLD χ s‖ + ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ := norm_add_le _ _
      _ ≤ 20 + C₀ := by linarith
      _ ≤ 4 * (20 + C₀) * L ^ 2 := by nlinarith
      _ ≤ _ := by nlinarith
  · have hσ' : s.re < 11 / 10 := lt_of_not_ge hσ
    have hshift : c₁ / 2 / L ≤ 1 / 27 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hσ1 : 26 / 27 ≤ s.re := by linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := by
      intro h0
      obtain ⟨β, hβ, hsβ⟩ := hBall s (zero_free_region_mono_half hc₁ q s hs) ⟨Or.inl hχ, h0⟩
      exact hsB β hβ hsβ
    obtain ⟨Z, m, hZ, hm3, hsum, hE⟩ := landau_lemma_lfunction_zeros hLL hC hInv hχ hσ1 hσ' hfs
    have hmain := log_deriv_sub_exceptional_zeros hc₁ hχ hBcard hBmem hBall hs hσ1 hσ' hZ hm3 hsum hE
    have hKL : 0 ≤ K₁ * L := by positivity
    have h4 : 0 ≤ 4 * (20 + C₀) * L ^ 2 := by positivity
    refine le_trans hmain ?_
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem siegel_theorem_of : SiegelOf := by
  intro hP hR hB hL1 hZ hLP hS ε hε
  obtain ⟨C, K, hK0, hKey⟩ := hB
  obtain ⟨CL, hL⟩ := hL1
  set σ₀ : ℝ := max (7 / 8) (1 - ε / (2 * (K + 1))) with hσ₀
  have hK1 : 0 < K + 1 := by linarith
  have h78 : 7 / 8 ≤ σ₀ := le_max_left _ _
  have hσ₀1 : σ₀ < 1 := by
    apply max_lt (by norm_num)
    have : 0 < ε / (2 * (K + 1)) := by positivity
    linarith
  have hKa : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → K * (1 - σ) ≤ ε / 2 := by
    intro σ hσ hσ1
    have h1 : 1 - ε / (2 * (K + 1)) ≤ σ := le_trans (le_max_right _ _) hσ
    have h2 : 1 - σ ≤ ε / (2 * (K + 1)) := by linarith
    have h3 : 0 ≤ 1 - σ := by linarith
    have h4 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by
      field_simp
    calc K * (1 - σ) ≤ (K + 1) * (1 - σ) := by nlinarith
      _ ≤ (K + 1) * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h2 hK1.le
      _ = ε / 2 := h4
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ σ₀ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0
  ·
    obtain ⟨q₁, hq₁, χ₁, β, h1sq, h1ne, hβ0, hβ1, hzero⟩ := hex
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne (le_trans h78 hβ0) hβ1
      (hKa β hβ0 hβ1) ?_
    intro q _ χ ψ _ _ _ _
    simp [Fbq, hzero]
  ·
    push_neg at hex
    obtain ⟨q₁, hq₁, χ₁, h1sq, h1ne⟩ := hR
    have hnz : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        ∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0 := by
      intro q _ χ hsq hne σ hσ
      rcases lt_or_ge σ 1 with h | h
      · exact hex q inferInstance χ σ hsq hne hσ h
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using h)
    have hpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        (DirichletCharacter.LFunction χ σ₀).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ₀).re := by
      intro q _ χ hsq hne
      exact hLP q χ hsq hne σ₀ (hnz q χ hsq hne) σ₀ le_rfl
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne h78 hσ₀1 (hKa σ₀ le_rfl hσ₀1) ?_
    intro q _ χ ψ hsq hne hψne hψ
    have hψsq := product_real_characters_sq_eq_one χ₁ χ ψ h1sq hsq hψ
    obtain ⟨hz_im, hz_re⟩ := hZ σ₀ (by linarith) hσ₀1
    obtain ⟨a_im, a_re⟩ := hpos q₁ χ₁ h1sq h1ne
    obtain ⟨b_im, b_re⟩ := hpos q χ hsq hne
    obtain ⟨c_im, c_re⟩ := hpos (q₁ * q) ψ hψsq hψne
    have hre : (Fbq χ₁ χ ψ σ₀).re = (riemannZeta σ₀).re * (DirichletCharacter.LFunction χ₁ σ₀).re *
        (DirichletCharacter.LFunction χ σ₀).re * (DirichletCharacter.LFunction ψ σ₀).re := by
      simp [Fbq, Complex.mul_re, Complex.mul_im, hz_im, a_im, b_im, c_im]
    rw [hre]
    have hp := mul_pos (mul_pos a_re b_re) c_re
    have hn := mul_neg_of_neg_of_pos hz_re hp
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound
section
open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_nonneg {w : ℂ} (h : 0 ≤ w.re) : 0 ≤ (1 / w).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg w)

lemma neg_re_le_norm (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  linarith [neg_le_abs x.re, Complex.abs_re_le_norm x]

private lemma re_natCast_div_nonneg (k : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ ((k : ℂ) / w).re := by
  have e : (k : ℂ) / w = ((k : ℝ) : ℂ) * (1 / w) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg k) (re_one_div_nonneg hw)

private lemma re_ge_and_norm_zeta_le_of_near_eleven_tenths {t : ℝ} (ht : 2 < |t|) {z : ℂ}
    (hz : ‖z - (((11 / 10 : ℝ) : ℂ) + t * I)‖ ≤ 3 / 5) :
    1 / 2 ≤ z.re ∧ z ≠ 1 ∧ ‖riemannZeta z‖ ≤ 6 * (|t| + 2) := by
  have h1 := Complex.abs_re_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have h2 := Complex.abs_im_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have er : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).re = z.re - 11 / 10 := by simp
  have ei : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).im = z.im - t := by simp
  rw [er] at h1
  rw [ei] at h2
  have hre := abs_le.mp (h1.trans hz)
  have h2' := h2.trans hz
  have him1 : |t| - |z.im| ≤ |z.im - t| := by rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub t z.im
  have him2 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
  have hzre : 1 / 2 ≤ z.re := by linarith [hre.1]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at h2'
    linarith
  have hd : 1 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hzn : ‖z‖ ≤ |t| + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have hr : |z.re| ≤ 17 / 10 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
    linarith
  have hg := Formalism.ZF.growthBound z (by linarith) hz1
  have hA : 1 / ‖z - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hd
  have hB : 1 / z.re ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hC : ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 3) * 3 :=
    mul_le_mul hzn (by linarith)
      (by have := one_div_pos.mpr (by linarith : (0 : ℝ) < z.re); linarith) (by positivity)
  refine ⟨hzre, hz1, ?_⟩
  linarith

lemma zeta_log_deriv_landau_bound (t σ : ℝ) (ht : 2 < |t|) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      840 * Real.log (|t| + 2) := by
  have hz0re : ((((11 / 10 : ℝ) : ℂ) + t * I)).re = 11 / 10 := by simp
  have hinv := Formalism.ZF.zetaInvBound_statement (((11 / 10 : ℝ) : ℂ) + t * I) (by rw [hz0re]; norm_num)
  have h1110 : (11 / 10 : ℝ) / (11 / 10 - 1) = 11 := by norm_num
  rw [hz0re, h1110] at hinv
  have hz0ne : riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; norm_num)
  have hpos : 0 < ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ := norm_pos_iff.mpr hz0ne
  have h11 : 1 ≤ ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ * 11 := by
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  have hT : 4 ≤ |t| + 2 := by linarith
  have hM1 : (1 : ℝ) ≤ 66 * (|t| + 2) := by linarith
  obtain ⟨Z, m, hZ, -, -, hbound⟩ := Formalism.ZF.landauLocal riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5)
    (66 * (|t| + 2)) (by norm_num) hM1
    (fun z hz => (differentiableAt_riemannZeta
      (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1).differentiableWithinAt)
    hz0ne
    (fun z hz => by
      have hb := (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.2
      nlinarith [mul_le_mul_of_nonneg_left h11 (by linarith : (0 : ℝ) ≤ 6 * (|t| + 2))])
  have hzmem : ((σ : ℂ) + t * I) ∈ Metric.closedBall (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5 / 6) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : (σ : ℂ) + t * I - (((11 / 10 : ℝ) : ℂ) + t * I) = ((σ - 11 / 10 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzre : ((σ : ℂ) + t * I).re = σ := by simp
  have hzne : riemannZeta ((σ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ)
  have hb := hbound _ hzmem hzne
  have hsum : 0 ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρ0 := ((hZ ρ).mp hρ).2
    have hρre : ρ.re ≤ 1 := by
      by_contra h
      push_neg at h
      exact riemannZeta_ne_zero_of_one_lt_re h hρ0
    apply re_natCast_div_nonneg
    simp
    linarith
  have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
      ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))
  have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
      (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
        ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))).re -
        (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    simp only [Complex.neg_re, Complex.sub_re]; ring
  have hlogM : Real.log (66 * (|t| + 2)) ≤ 7 * Real.log (|t| + 2) := by
    have h6 : (4 : ℝ) ^ 6 ≤ (|t| + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) hT 6
    have hle : 66 * (|t| + 2) ≤ (|t| + 2) ^ 7 := by
      have e7 : (|t| + 2) ^ 7 = (|t| + 2) ^ 6 * (|t| + 2) := by ring
      rw [e7]; nlinarith
    calc Real.log (66 * (|t| + 2)) ≤ Real.log ((|t| + 2) ^ 7) := Real.log_le_log (by linarith) hle
      _ = 7 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num
  have h72 : 72 * Real.log (66 * (|t| + 2)) / (3 / 5) = 120 * Real.log (66 * (|t| + 2)) := by ring
  rw [hsplit]
  linarith

lemma zeta_neg_log_deriv_re_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + K * Real.log (|t| + 2) := by
  obtain ⟨c, C, hc, hreg⟩ := Formalism.ZF.logDerivRegion
  obtain ⟨K₃, hK₃⟩ : ∃ k : ℝ, k = ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((6 / 5 : ℝ) : ℂ) n‖ := ⟨_, rfl⟩
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨840 + |C| * Real.log 4 + |K₃|,
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hlog4)) (abs_nonneg _), ?_⟩
  intro σ t hσ hσ2
  have hre1 : 0 ≤ ((σ : ℂ) - 1 + t * I).re := by simp; linarith
  have hR := re_one_div_nonneg hre1
  have hL0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hC0 : 0 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := mul_nonneg (mul_nonneg (abs_nonneg _) hlog4) hL0
  have hK30 : 0 ≤ |K₃| * Real.log (|t| + 2) := mul_nonneg (abs_nonneg _) hL0
  have h840 : 0 ≤ 840 * Real.log (|t| + 2) := mul_nonneg (by norm_num) hL0
  rcases le_or_gt |t| 2 with ht | ht
  ·
    have hs1 : ((σ : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have hsre : ((σ : ℂ) + t * I).re = σ := by simp
    have hLpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
    have hcond : 1 - c / Real.log (|((σ : ℂ) + t * I).im| + 2) ≤ ((σ : ℂ) + t * I).re := by
      rw [him, hsre]; have := div_nonneg hc.le hLpos.le; linarith
    have hb := hreg _ hs1 hcond
    rw [him] at hb
    have es : (σ : ℂ) + t * I - 1 = (σ : ℂ) - 1 + t * I := by ring
    rw [es] at hb
    have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) +
      1 / ((σ : ℂ) - 1 + t * I))
    have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
        (1 / ((σ : ℂ) - 1 + t * I)).re + (-(deriv riemannZeta ((σ : ℂ) + t * I) /
          riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))).re := by
      simp only [Complex.neg_re, Complex.add_re]; ring
    have hL4 : Real.log (|t| + 2) ≤ Real.log 4 :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hCL : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := by
      have h1 : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log (|t| + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      have h2 : |C| * (Real.log (|t| + 2) * Real.log (|t| + 2)) ≤ |C| * (Real.log 4 * Real.log (|t| + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL4 hL0) (abs_nonneg C)
      nlinarith
    rw [hsplit]
    nlinarith
  rcases le_or_gt σ (6 / 5) with hσ' | hσ'
  ·
    have := zeta_log_deriv_landau_bound t σ ht hσ hσ'
    nlinarith
  ·
    have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
    have hLs := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
    rw [neg_div] at hLs
    rw [← hLs]
    have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
    have hsum0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((6 / 5 : ℝ) : ℂ))
      (by rw [Complex.ofReal_re]; norm_num)
    have hbd : (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re ≤ K₃ := by
      calc (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re
          ≤ ‖LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖ :=
            Complex.re_le_norm _
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((6 / 5 : ℝ) : ℂ) n‖ :=
            Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simp; linarith) n)
              (summable_norm_iff.mpr hsum) (summable_norm_iff.mpr hsum0)
        _ = K₃ := hK₃.symm
    have hL1 : 1 ≤ Real.log (|t| + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hK3 : K₃ ≤ |K₃| * Real.log (|t| + 2) := by
      have := mul_le_mul_of_nonneg_left hL1 (abs_nonneg K₃)
      linarith [le_abs_self K₃]
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end

