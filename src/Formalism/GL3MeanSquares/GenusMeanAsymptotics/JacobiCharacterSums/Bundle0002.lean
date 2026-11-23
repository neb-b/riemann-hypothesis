module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmA
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem num_alg (M y C D Pt t lg lm : ℝ) (hM : 1 ≤ M) (hy : M ^ 5 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPt : Pt ≤ (M ^ 8)⁻¹) (ht : t ≤ (M ^ 2)⁻¹) (hlg : lg ≤ D * M ^ 2)
    (hlm0 : 0 ≤ lm) (hlm : lm ≤ 13 * M) :
    M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * t ≤ (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hA : M ^ 6 * Pt ≤ (M ^ 2)⁻¹ := by
    calc M ^ 6 * Pt ≤ M ^ 6 * (M ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hPt (by positivity)
      _ = (M ^ 2)⁻¹ := by field_simp
  have hB : lg * lm ^ 2 / M ^ 6 ≤ 169 * D * (M ^ 2)⁻¹ := by
    have hlm2 : lm ^ 2 ≤ 169 * M ^ 2 := by nlinarith
    have h2 : lg * lm ^ 2 ≤ D * M ^ 2 * (169 * M ^ 2) :=
      calc lg * lm ^ 2 ≤ D * M ^ 2 * lm ^ 2 := mul_le_mul_of_nonneg_right hlg (sq_nonneg _)
        _ ≤ D * M ^ 2 * (169 * M ^ 2) := mul_le_mul_of_nonneg_left hlm2 (by positivity)
    calc lg * lm ^ 2 / M ^ 6 ≤ D * M ^ 2 * (169 * M ^ 2) / M ^ 6 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 169 * D * (M ^ 2)⁻¹ := by field_simp <;> ring
  have e1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      = 4 * C * y * (M ^ 6 * Pt + lg * lm ^ 2 / M ^ 6) := by
    field_simp <;> ring
  have h1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      ≤ 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) := by
    rw [e1]; exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hM3 : M ^ 3 ≤ y * (M ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]; calc M ^ 3 * M ^ 2 = M ^ 5 := by ring
      _ ≤ y := hy
  have h2 : M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) ≤ 8 * D * y * (M ^ 2)⁻¹ := by
    have hc : 0 ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) := by positivity
    calc M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) = 4 * M * ((M ^ 5)⁻¹ * y + 1) * lg := by ring
      _ ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) * (D * M ^ 2) := mul_le_mul_of_nonneg_left hlg hc
      _ = 4 * D * (y * (M ^ 2)⁻¹ + M ^ 3) := by field_simp <;> ring
      _ ≤ 4 * D * (y * (M ^ 2)⁻¹ + y * (M ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * D * y * (M ^ 2)⁻¹ := by ring
  have h5 : (M ^ 5)⁻¹ ≤ (M ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hM (by norm_num))
  have h3 : 20 * (M ^ 5)⁻¹ * y ≤ 20 * (M ^ 2)⁻¹ * y := by
    have := mul_le_mul_of_nonneg_right h5 hy0; linarith
  have h4 : 2 * y * t ≤ 2 * y * (M ^ 2)⁻¹ := mul_le_mul_of_nonneg_left ht (by positivity)
  have e2 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
      = M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
        + M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) := by ring
  rw [e2]
  have e3 : (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹
      = 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) + 8 * D * y * (M ^ 2)⁻¹
        + 20 * (M ^ 2)⁻¹ * y + 2 * y * (M ^ 2)⁻¹ := by ring
  rw [e3]
  linarith

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3

theorem inv_pow_eq_exp {M : ℝ} (hM : 0 < M) (n : ℕ) : (M ^ n)⁻¹ = Real.exp (-(n * Real.log M)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hM n)]

theorem logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2

theorem inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by
  have hM0 : 0 < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 := logy_lt hcA hy h
  have h3 : c * Real.log y ≤ Real.log M ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc' hly]
  have h4 : c * Real.log y / Real.log M ≤ Real.log M := by
    rw [div_le_iff₀ hlM]; nlinarith
  calc M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM0]
    _ ≤ Real.exp (-(c * Real.log y / Real.log M)) := Real.exp_le_exp.mpr (by linarith)

theorem num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by
  set D : ℝ := 1 + (cA ^ 2)⁻¹ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨5 + (26 * C + 20) / κ, 4 * C + 676 * C * D + 8 * D + 22, by positivity, by positivity, ?_⟩
  intro M y hM hy hlog hsq
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hl1 : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hLM : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM0]
  have hC0 : 0 ≤ 5 + (26 * C + 20) / κ := by positivity
  have hlog' : (5 + (26 * C + 20) / κ) * Real.log M ≤ Real.log y := by
    have : (5 + (26 * C + 20) / κ) * Real.log M * 1
        ≤ (5 + (26 * C + 20) / κ) * Real.log M * Real.log (Real.log M + 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hkC : κ * (5 + (26 * C + 20) / κ) = 5 * κ + (26 * C + 20) := by field_simp
  have hK : (26 * C + 20) * Real.log M ≤ κ * Real.log y := by
    have := mul_le_mul_of_nonneg_left hlog' hκ.le
    have h5 : 0 ≤ 5 * κ * Real.log M := by positivity
    nlinarith
  have hy5 : M ^ 5 ≤ y := by
    rw [← Real.log_le_log_iff (by positivity) hy0, Real.log_pow]
    have : 5 * Real.log M ≤ (5 + (26 * C + 20) / κ) * Real.log M := by
      have : 0 ≤ (26 * C + 20) / κ * Real.log M := by positivity
      nlinarith
    push_cast; linarith
  have h12 : M ^ (12 : ℝ) = M ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h12]
  have hlm : Real.log (M * M ^ 12) = 13 * Real.log M := by
    rw [show M * M ^ 12 = M ^ 13 by ring, Real.log_pow]; push_cast; ring
  have hpow : (M * M ^ 12) ^ C = Real.exp (13 * C * Real.log M) := by
    rw [Real.rpow_def_of_pos (by positivity), hlm]; ring_nf
  have hyk : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  have hPt : (M * M ^ 12) ^ C * y ^ (-(κ / 2)) ≤ (M ^ 8)⁻¹ := by
    rw [hpow, hyk, ← Real.exp_add, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have ht : y ^ (-(κ / 2)) ≤ (M ^ 2)⁻¹ := by
    rw [hyk, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    have : 0 ≤ 26 * C * Real.log M := by positivity
    nlinarith
  have hlg : Real.log (2 * y) ≤ D * M ^ 2 := by
    have hq := logy_lt hcA hy hsq
    have hq' : Real.log y ≤ Real.log M ^ 2 * (cA ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    have hLM2 : Real.log M ^ 2 ≤ M ^ 2 := by nlinarith
    have hq'' : Real.log M ^ 2 * (cA ^ 2)⁻¹ ≤ M ^ 2 * (cA ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hLM2 (by positivity)
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hM1 : 1 ≤ M ^ 2 := by nlinarith
    rw [Real.log_mul (by norm_num) hy0.ne', hDdef]
    nlinarith
  have hlm0 : 0 ≤ Real.log (M * M ^ 12) := by rw [hlm]; linarith
  have hlm13 : Real.log (M * M ^ 12) ≤ 13 * M := by rw [hlm]; linarith
  have key := num_alg M y C D ((M * M ^ 12) ^ C * y ^ (-(κ / 2))) (y ^ (-(κ / 2)))
    (Real.log (2 * y)) (Real.log (M * M ^ 12)) (by linarith) hy5 hC.le hD hPt ht hlg hlm0 hlm13
  refine key.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeB
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma dhpr_pow_exp_le (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by
  have hx : 0 ≤ b * t := mul_nonneg hb ht
  have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (b * t) hx m
    rwa [div_le_iff₀ hf] at h
  calc b ^ m * (t ^ m * Real.exp (-(b * t))) = (b * t) ^ m * Real.exp (-(b * t)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
        rw [mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]; simp

lemma dhpr_one_sub_exp_neg {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith
  have h4 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hpos]
  have e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a) := by ring
  rw [e]; linarith

lemma dhpr_pow_ratio (m : ℕ) : ((m : ℝ) + 1) ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [pow_zero, mul_one]
    linarith [Real.add_one_le_exp (1:ℝ)]
  · have hm : (0:ℝ) < m := by exact_mod_cast h
    have hm' : (m:ℝ) ≠ 0 := hm.ne'
    have key : (m:ℝ) + 1 ≤ m * Real.exp (1 / m) := by
      have h1 := Real.add_one_le_exp (1 / (m:ℝ))
      have h2 : (m:ℝ) * (1 / m + 1) = m + 1 := by
        rw [mul_add, mul_one_div_cancel hm', mul_one, add_comm]
      calc (m:ℝ) + 1 = m * (1 / m + 1) := h2.symm
        _ ≤ m * Real.exp (1 / m) := mul_le_mul_of_nonneg_left h1 hm.le
    calc ((m:ℝ) + 1) ^ m ≤ ((m:ℝ) * Real.exp (1 / m)) ^ m := by gcongr
      _ = Real.exp 1 * (m:ℝ) ^ m := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hm', mul_comm]

lemma dhpr_wsup (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v : ℕ) :
    ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 1 * m.factorial / η ^ m := by
  have hηm : 0 < η ^ m := pow_pos hη m
  have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
  have h1 := dhpr_pow_exp_le m hη.le ht
  have h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η) := by ring
    rw [e]; linarith
  calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * v))
      ≤ ((v : ℝ) + 1) ^ m * (Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp 1 * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
    _ ≤ Real.exp 1 * ((m.factorial : ℝ) / η ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        rw [le_div_iff₀ hηm]
        calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1))) * η ^ m
            = η ^ m * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
          _ ≤ (m.factorial : ℝ) := h1
    _ = Real.exp 1 * m.factorial / η ^ m := by ring

lemma dhpr_wsum (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) / η ^ (m + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hm1ne : (m:ℝ) + 1 ≠ 0 := hm1.ne'
  have hδη : ((m:ℝ) + 1) * δ = η := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hη hm1
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hη'nn : 0 ≤ (m:ℝ) * δ := mul_nonneg hm0 hδpos.le
  have hsplit : (m:ℝ) * δ + δ = η := by rw [← hδη]; ring
  have hη'le : (m:ℝ) * δ ≤ 1 := by linarith
  have hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m := by
    rw [← hδη, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)
  have hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤
      Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
    intro v
    have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
    have h1 := dhpr_pow_exp_le m hη'nn ht
    have hexp : Real.exp (-(η * v)) ≤
        Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hsplit]
      have e : -(((m:ℝ) * δ + δ) * (v:ℝ)) =
          1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ) := by ring
      rw [e]; linarith
    calc η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v)))
        ≤ (Real.exp 1 * ((m:ℝ) * δ) ^ m) * (((v:ℝ) + 1) ^ m *
            (Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)))) := by
          refine mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m *
            Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          rw [← Real.exp_add]; norm_num
  have hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ := by
    have hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v := by
      intro v; rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hrw]
    have hr0 : 0 < Real.exp (-δ) := Real.exp_pos _
    have hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        exact hx.2
      · intro i _ _
        exact pow_nonneg hr0.le i
    have hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1 := by
      have h := geom_sum_mul (Real.exp (-δ)) V
      have hV : 0 ≤ Real.exp (-δ) ^ V := pow_nonneg hr0.le V
      have e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) =
          -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1)) := by ring
      rw [e, h]; linarith
    have h2 := dhpr_one_sub_exp_neg hδpos
    have h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ) := by
      rwa [div_le_iff₀ (by linarith)] at h2
    calc (∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v) * δ
        ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * δ := mul_le_mul_of_nonneg_right hsub hδpos.le
      _ ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * ((1 - Real.exp (-δ)) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left h2' hG0
      _ = ((∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ))) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := mul_le_mul_of_nonneg_right hgeo (by linarith)
      _ = 1 + δ := one_mul _
  rw [le_div_iff₀ (pow_pos hη (m + 1))]
  calc (∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η ^ (m + 1)
      = (η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η := by ring
    _ ≤ (Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * η :=
        mul_le_mul_of_nonneg_right hsum hη.le
    _ = Real.exp 2 * (m.factorial : ℝ) * ((∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ) *
          ((m:ℝ) + 1) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (1 + δ) * ((m:ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hm1.le
        exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring

lemma dhpr_esum (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)) ≤
      20 * Real.exp (-((v0 : ℝ) / 4)) := by
  have hr0 : 0 < Real.exp (-(1/4:ℝ)) := Real.exp_pos _
  have hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v := by
    intro v
    have h1 := Real.add_one_le_exp ((v:ℝ) / 4)
    have hv : (0:ℝ) ≤ v := Nat.cast_nonneg v
    calc ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2))
        ≤ (4 * Real.exp ((v:ℝ) / 4)) * Real.exp (-((v:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 4 * (Real.exp ((v:ℝ) / 4) * Real.exp (-((v:ℝ) / 2))) := by ring
      _ = 4 * Real.exp (-(1/4:ℝ)) ^ v := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
  have h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ)) := by
    have h := dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)
    have e : (1/4:ℝ) / (1 + 1/4) = 1 / 5 := by norm_num
    rw [e] at h
    exact h
  have hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]
    have hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have h := geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)
    have hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0) := pow_nonneg hr0.le _
    have hmul := mul_le_mul_of_nonneg_left h15 hG0
    have hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5 := by
      have e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) =
          -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1)) := by ring
      rw [h] at e
      linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)
  calc ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))
      ≤ ∑ v ∈ Ico v0 V, 4 * Real.exp (-(1/4:ℝ)) ^ v := Finset.sum_le_sum (fun v _ => hterm v)
    _ = 4 * ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v := by rw [Finset.mul_sum]
    _ ≤ 4 * (5 * Real.exp (-(1/4:ℝ)) ^ v0) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 20 * Real.exp (-((v0 : ℝ) / 4)) := by
        rw [← Real.exp_nat_mul]
        have e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4) := by ring
        rw [e]; ring

lemma dhpr_floor_mono {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ :=
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))

lemma dhpr_blocks (g : ℕ → ℝ) (v0 : ℕ) : ∀ V, v0 ≤ V →
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, g n =
      ∑ v ∈ Ico v0 V, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, g n := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    exact (Finset.sum_Ioc_consecutive g (dhpr_floor_mono hn)
      (dhpr_floor_mono (by omega : n ≤ n + 1))).symm

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharpA
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma sharp_cpow_sub_one {ρ : ℂ} (hρ0 : ρ ≠ 0) (hre : ρ.re ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (t - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)
    calc ‖ρ‖ * x ^ (ρ - 1).re ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

lemma differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  let f : ℝ → ℂ := fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)
  let f' : ℝ → ℂ := fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
    have h1 := (((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1)
      (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)
    have h2 := ((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    have e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2 := by
      rw [show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [e1]
    push_cast
    field_simp
    ring
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hk := sharp_cpow_sub_one hρ0 hre hx.1
    simp only [f']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hx1 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
    calc ‖(x : ℂ) ^ ρ - 1‖ / x ^ 2 ≤ ‖(x : ℂ) ^ ρ - 1‖ := div_le_self (norm_nonneg _) hx1
      _ ≤ ‖ρ‖ * (x - 1) := hk
      _ ≤ ‖ρ‖ * δ := by gcongr; linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1, sub_zero, show 1 + δ - 1 = δ by ring] at h
  exact h

lemma sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by
  set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg
  set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he
  have hae := differenced_kernel_bound hρ0 hρ1 hre hδ
  rw [← hg, ← he] at hae
  have hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1 := by
    field_simp
    ring
  have hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e := by
    rw [he, mul_add, ← Complex.ofReal_mul, hr]
    push_cast
    ring
  have hq : 0 < (1 + δ) / δ := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc (1 + δ) / δ * ‖e‖ ≤ (1 + δ) / δ * (‖ρ‖ * δ * δ) := by gcongr
    _ = (1 + δ) * (δ * ‖ρ‖) := by field_simp
    _ ≤ 2 * (δ * ‖ρ‖) := by gcongr; linarith
    _ = 2 * δ * ‖ρ‖ := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

