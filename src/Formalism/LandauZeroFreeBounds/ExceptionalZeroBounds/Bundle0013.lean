module

public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0011
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0002
public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0002
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0012

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
section
open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_le_of_log_bound {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h3 : (0 : ℝ) ≤ 3 * q := by positivity
  have hl0 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hl : Real.log (3 * q) ≤ 3 * q := Real.log_le_self h3
  calc ‖z‖ ≤ CL * Real.log (3 * q) := h
    _ ≤ |CL| * Real.log (3 * q) := mul_le_mul_of_nonneg_right (le_abs_self CL) hl0
    _ ≤ |CL| * (3 * q) := mul_le_mul_of_nonneg_left hl (abs_nonneg CL)

lemma exists_taylor_truncation_order (T : ℝ) (hT : 1 ≤ T) :
    ∃ M : ℕ, 1 ≤ M ∧ T * (3 / 4 : ℝ) ^ M ≤ 1 ∧ (M : ℝ) ≤ Real.log T / Real.log (4 / 3) + 2 := by
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.log T / Real.log (4 / 3) := div_nonneg (Real.log_nonneg hT) hl43.le
  refine ⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩
  · have hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]
    have hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3) := by
      have h := mul_le_mul_of_nonneg_right hM hl43.le
      rwa [div_mul_cancel₀ _ hl43.ne'] at h
    have hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp (((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)) :=
          Real.exp_le_exp.mpr hlog
        _ = (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by positivity
    calc T * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)
        ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) :=
          mul_le_mul_of_nonneg_right hT' hp.le
      _ = 1 := h34
  · push_cast
    linarith [Nat.ceil_lt_add_one hx0]

lemma two_sub_pow_le_exp {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by
  have h1 : 0 < 1 - σ := by linarith
  have hb : 2 - σ ≤ Real.exp (1 - σ) := by
    have := Real.add_one_le_exp (1 - σ); linarith
  have hb0 : 0 ≤ 2 - σ := by linarith
  calc (2 - σ) ^ M ≤ Real.exp (1 - σ) ^ M := pow_le_pow_left₀ hb0 hb M
    _ = Real.exp (M * (1 - σ)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (A + P * (1 - σ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]
    _ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _

theorem product_lfunction_key_inequality : BqKeyOf := by
  intro hCoeff hEnt hGrow hL1
  obtain ⟨Cg, Kg, hg⟩ := hGrow
  obtain ⟨CL, hL⟩ := hL1
  obtain ⟨c0, hc0def⟩ : ∃ c : ℝ, c = |Cg| + 54 * |CL| ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K', hK'def⟩ : ∃ k : ℝ, k = max Kg 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ l : ℝ, l = Real.log (4 / 3) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by norm_num)
  have hc0 : 1 ≤ c0 := by
    rw [hc0def]; have := abs_nonneg Cg; have := pow_nonneg (abs_nonneg CL) 3; linarith
  have hKgK : Kg ≤ K' := by rw [hK'def]; exact le_max_left _ _
  have h2K : (2 : ℝ) ≤ K' := by rw [hK'def]; exact le_max_right _ _
  refine ⟨Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)), K' / ℓ,
    div_nonneg (by linarith) hℓ.le, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h1ne h2ne hψne hψ σ hσ1 hσ2
  have h1σ : 0 < 1 - σ := by linarith
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : (1 : ℝ) ≤ q₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hN : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by rw [hN]; nlinarith
  obtain ⟨a, ha0, ha1, habs, hFa⟩ := hCoeff q₁ q₂ χ₁ χ₂ ψ h1 h2 hψ
  obtain ⟨G, hG, hFG⟩ := hEnt q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne
  have hlam : ‖lamBq χ₁ χ₂ ψ‖ ≤ 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by
    have e1 := norm_le_of_log_bound q₁ (hL q₁ χ₁ h1ne)
    have e2 := norm_le_of_log_bound q₂ (hL q₂ χ₂ h2ne)
    have e3 := norm_le_of_log_bound (q₁ * q₂) (hL (q₁ * q₂) ψ hψne)
    simp only [lamBq, norm_mul]
    calc _ ≤ (|CL| * (3 * q₁)) * (|CL| * (3 * q₂)) * (|CL| * (3 * ((q₁ * q₂ : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) (by positivity)) e3 (norm_nonneg _) (by positivity)
      _ = 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by rw [hN]; ring
  have hKg : ((q₁ * q₂ : ℕ) : ℝ) ^ Kg ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' :=
    Real.rpow_le_rpow_of_exponent_le hN1 hKgK
  have hK2 : ((q₁ * q₂ : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hNK0 : 0 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by positivity
  have hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    intro s hs
    rw [mem_sphere_iff_norm] at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    have hd : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h := norm_sub_le (s - 1) (1 : ℂ)
      have e : s - 1 - 1 = s - 2 := by ring
      rw [e, hs, norm_one] at h
      linarith
    have hGs : G s = Fbq χ₁ χ₂ ψ s - lamBq χ₁ χ₂ ψ / (s - 1) := by rw [hFG s hs1]; ring
    have hF := hg q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne s hs
    have hdiv : ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ ≤ 2 * ‖lamBq χ₁ χ₂ ψ‖ := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lamBq χ₁ χ₂ ψ)]
    have hc3 : 0 ≤ 54 * |CL| ^ 3 := by positivity
    calc ‖G s‖ ≤ ‖Fbq χ₁ χ₂ ψ s‖ + ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ := by rw [hGs]; exact norm_sub_le _ _
      _ ≤ Cg * ((q₁ * q₂ : ℕ) : ℝ) ^ Kg + 2 * (27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2) := by linarith
      _ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
        rw [hc0def]
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cg) (by positivity : (0 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ Kg),
          mul_le_mul_of_nonneg_left hKg (abs_nonneg Cg), mul_le_mul_of_nonneg_left hK2 hc3]
  have hNK1 : 1 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := Real.one_le_rpow hN1 (by linarith)
  have hT : 1 ≤ 8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') := by
    nlinarith [mul_le_mul hc0 hNK1 zero_le_one (by linarith)]
  obtain ⟨M, hM1, hTM, hMle⟩ := exists_taylor_truncation_order _ hT
  rw [← hℓdef] at hMle
  have hcore := lseries_taylor_lower_bound ha0 ha1 habs hG hFa hFG hB hσ1 hσ2 hM1
  have hpow := two_sub_pow_le_exp (A := 2) (P := Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ)
    (M := M) (by norm_num) hσ1 hσ2 (by linarith)
  have hlogT : Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) =
      Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [← mul_assoc, Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  have hlogc : 0 ≤ Real.log (8 * c0) := Real.log_nonneg (by linarith)
  have hexp : Real.exp (Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ * (1 - σ)) ≤
      Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) by linarith) (K' / ℓ * (1 - σ)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlogT]
    have eL : (Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)) / ℓ * (1 - σ) =
        (Real.log (8 * c0) * (1 - σ) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    have eR : Real.log (8 * c0) / (8 * ℓ) + Real.log ((q₁ * q₂ : ℕ) : ℝ) * (K' / ℓ * (1 - σ)) =
        (Real.log (8 * c0) / 8 + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    rw [eL, eR]
    apply div_le_div_of_nonneg_right _ hℓ.le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1 / 8) hlogc]
  have hpow' : (2 - σ) ^ M ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) *
      ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) :=
    hpow.trans ((mul_le_mul_of_nonneg_left hexp (Real.exp_pos 2).le).trans_eq (by ring))
  have h34 : 4 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') * (3 / 4 : ℝ) ^ M ≤ 1 / 2 := by linarith
  have hlam0 := norm_nonneg (lamBq χ₁ χ₂ ψ)
  have hdiv : ‖lamBq χ₁ χ₂ ψ‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ‖lamBq χ₁ χ₂ ψ‖ *
        ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ h1σ.le
    nlinarith [mul_le_mul_of_nonneg_left hpow' hlam0]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExpGainFromZeroFreeRegion
section
noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem perron_error_terms_sum_bound (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by nlinarith
  have hX1 : X ≤ 1 := by nlinarith
  have e1 : ∀ z : ℝ, z / T = z * X := fun z => by
    rw [div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]
  have e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X := fun z => by
    rw [div_eq_iff (pow_pos hT0 2).ne']
    calc z = z * (T * X) * (T * X) := by rw [hTX]; ring
      _ = z * X * X * T ^ 2 := by ring
  simp only [e1, e2]
  have hPw : 0 ≤ Pw := by linarith
  have hyX : 0 ≤ y * X := mul_nonneg hy0.le hX0.le
  have hTY : 0 ≤ T * Y := mul_nonneg hT0.le hY
  have hcC : 0 ≤ C / c₁ := div_nonneg hC hc₁.le
  have hc2 : 0 ≤ 24 / c₁ ^ 2 := by positivity
  have h8 : 0 ≤ 8 / c₁ := div_nonneg (by norm_num) hc₁.le
  have k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
  have k2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
  have k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) := mul_nonneg (by norm_num) (add_nonneg hcC hc2)
  have h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤
      2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X) := by
    have hA : ℓ + C₀ ≤ (1 + C₀) * Pw := by nlinarith
    have hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X) := mul_nonneg (by positivity) hyX
    have := mul_le_mul_of_nonneg_left hA hk
    linarith
  have hB0 : 0 ≤ C * L ^ 2 + 1 := add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one
  have hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw := by
    linarith [mul_le_mul_of_nonneg_left hL2P hC]
  have hXX : X * X ≤ X := mul_le_of_le_one_right hX0.le hX1
  have h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X) := by
    have s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X := mul_le_mul_of_nonneg_left hXX hB0
    have s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X := mul_le_mul_of_nonneg_right hB hX0.le
    have s3 := mul_le_mul_of_nonneg_left (s1.trans s2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))
    linarith
  have h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤
      16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y) := by
    have hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) =
        (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ hTY
    linarith [mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]
  have h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y) := by
    have hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y := by ring
    rw [hid]
    have s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw := mul_le_mul_of_nonneg_left hLP h8
    have s2 : Y ≤ T * Y := by nlinarith
    calc 8 / c₁ * L * Y ≤ 8 / c₁ * Pw * Y := mul_le_mul_of_nonneg_right s1 hY
      _ ≤ 8 / c₁ * Pw * (T * Y) := mul_le_mul_of_nonneg_left s2 (mul_nonneg h8 hPw)
  nlinarith [mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY,
    mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]

theorem exp_gain_from_zero_free_region (y s c₁ σ₁ L : ℝ) (hy0 : 0 < y) (hℓ : Real.log y = s ^ 2) (hs0 : 0 < s)
    (hc₁ : 0 < c₁) (hL : 0 < L) (hL4 : 4 * L ≤ s) (hσ : σ₁ ≤ 1 - c₁ / (4 * L)) :
    Real.exp (c₁ * s / 2) * y ^ σ₁ ≤ y * Real.exp (-(c₁ * s / 2)) := by
  have hy : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy0]
  have hyσ : y ^ σ₁ = Real.exp (s ^ 2 * σ₁) := by rw [Real.rpow_def_of_pos hy0, hℓ]
  rw [hyσ, ← Real.exp_add, hy, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h4L : 0 < 4 * L := by linarith
  have hq : c₁ ≤ c₁ / (4 * L) * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h4L]; nlinarith
  have hc : c₁ ≤ (1 - σ₁) * s := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : c₁ / (4 * L) ≤ 1 - σ₁) hs0.le]
  nlinarith [mul_le_mul_of_nonneg_right hc hs0.le]

theorem small_scale_exp_bounds (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by
  constructor
  · have h : c₁ * s / 2 ≤ 1 := by nlinarith
    calc Real.exp (c₁ * s / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · have h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s := by nlinarith
    have := Real.add_one_le_exp (-(c₁ / 4) * s)
    linarith

theorem cube_mul_exp_le_poly_bound (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by
  have hu0 : 0 < c₁ * s / 4 := div_pos (mul_pos hc₁ hs0) (by norm_num)
  have hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4) := by
    have h := Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3
    norm_num [Nat.factorial] at h
    linarith
  have hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4)) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4)) := by congr 1; ring
  rw [he, hX']
  have hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 := by
    have h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4))
      (Real.exp_pos (-(c₁ * s / 4))).le
    linarith
  have hsu : s = 8 / (2 * c₁) * (c₁ * s / 4) := by
    have := hc₁.ne'
    field_simp
    try ring
  have hK : 0 ≤ (8 / (2 * c₁)) ^ 3 := pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3
  have key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3 := by
    have hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3 := by
      rw [← mul_pow, ← hsu]
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hK]
  nlinarith [mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]

end Formalism.ZeroFreeDirichlet
end
end

