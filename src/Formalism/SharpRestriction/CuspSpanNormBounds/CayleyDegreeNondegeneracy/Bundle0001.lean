module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassPowLeExpRpow
section
namespace Formalism.MainNotions.BridgeLemma₂

private theorem const_20736_le_exp_15 : (20736 : ℝ) ≤ Real.exp 15 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (20736 : ℝ) ≤ 2 ^ 15 := by norm_num
    _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) h1 15

theorem mass_pow_le_exp_rpow (f m : ℕ) (rd L B₁ C κ : ℝ) (hf : 1 ≤ f) (hm : 2 ≤ m) (hrd : 2 ≤ rd) (hL : 1 ≤ L) (hκ : 1 ≤ κ)
    (hlf : Real.log f ≤ m) (hlrd : Real.log rd ≤ κ * L) (hB0 : 0 ≤ B₁) (hB : B₁ ≤ 4 * f * rd) (hC : 55 * κ ≤ C ^ 2) :
    (1 + 2 * B₁) ^ (2 * (2 * f)) * (1 + 2 * (B₁ * rd)) ^ (2 * (2 * f)) * (B₁ * (B₁ * rd)) ^ (4 * (2 * f)) ≤
      (Real.exp L ^ (C * (m : ℝ) ^ 2 * f)) ^ C := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hfpos : (0 : ℝ) < f := by linarith
  have hrdpos : (0 : ℝ) < rd := by linarith
  have hfe : (f : ℝ) ≤ Real.exp m := (Real.log_le_iff_le_exp hfpos).1 hlf
  have hre : rd ≤ Real.exp (κ * L) := (Real.log_le_iff_le_exp hrdpos).1 hlrd
  have hfr : (1 : ℝ) ≤ f * rd := by nlinarith
  have hfr2 : (1 : ℝ) ≤ f * rd ^ 2 := by nlinarith
  have hBr0 : 0 ≤ B₁ * rd := mul_nonneg hB0 hrdpos.le
  have hBr : B₁ * rd ≤ 4 * f * rd * rd := mul_le_mul_of_nonneg_right hB hrdpos.le
  have ha : 1 + 2 * B₁ ≤ 9 * f * rd := by nlinarith
  have hb : 1 + 2 * (B₁ * rd) ≤ 9 * f * rd ^ 2 := by nlinarith
  have hc : B₁ * (B₁ * rd) ≤ 16 * (f : ℝ) ^ 2 * rd ^ 3 := by
    have h := mul_le_mul hB hBr hBr0 (by linarith)
    calc B₁ * (B₁ * rd) ≤ 4 * f * rd * (4 * f * rd * rd) := h
      _ = 16 * (f : ℝ) ^ 2 * rd ^ 3 := by ring
  have hQ0 : 0 ≤ (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hQ : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
      Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) := by
    have hc2 : (B₁ * (B₁ * rd)) ^ 2 ≤ (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hB0 hBr0) hc 2
    have hab : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) ≤ (9 * f * rd) * (9 * f * rd ^ 2) :=
      mul_le_mul ha hb (by linarith) (by linarith)
    have h1 : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
        (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      mul_le_mul hab hc2 (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    have h2 : (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 =
        20736 * (f : ℝ) ^ 6 * rd ^ 9 := by ring
    have hf6 : (f : ℝ) ^ 6 ≤ Real.exp m ^ 6 := pow_le_pow_left₀ hfpos.le hfe 6
    have hr9 : rd ^ 9 ≤ Real.exp (κ * L) ^ 9 := pow_le_pow_left₀ hrdpos.le hre 9
    have h3 : 20736 * (f : ℝ) ^ 6 * rd ^ 9 ≤ Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 :=
      mul_le_mul (mul_le_mul const_20736_le_exp_15 hf6 (by positivity) (by positivity)) hr9
        (pow_nonneg hrdpos.le 9) (by positivity)
    have h4 : Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 := by
      rw [Real.exp_add, Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    rw [h4]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  have key : 60 + 24 * (m : ℝ) + 36 * (κ * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) := by
    have y1 : 1 ≤ κ * L := by nlinarith
    have hmm : 2 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hyl : (m : ℝ) ^ 2 ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hy4 : 4 * (κ * L) ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hCk : 55 * κ * ((m : ℝ) ^ 2 * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
    nlinarith
  have hexp : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) ≤
      L * (C * (m : ℝ) ^ 2 * f) * C := by
    have e1 : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        (f : ℝ) * (60 + 24 * (m : ℝ) + 36 * (κ * L)) := by push_cast; ring
    have e2 : L * (C * (m : ℝ) ^ 2 * f) * C = (f : ℝ) * (C ^ 2 * ((m : ℝ) ^ 2 * L)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hfpos.le
  have hpow : 4 * (2 * f) = 2 * (2 * (2 * f)) := by ring
  rw [hpow, pow_mul (B₁ * (B₁ * rd)) 2 (2 * (2 * f)), ← mul_pow, ← mul_pow, ← Real.exp_mul,
    ← Real.exp_mul]
  calc _ ≤ (Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L))) ^ (2 * (2 * f)) :=
        pow_le_pow_left₀ hQ0 hQ _
    _ = Real.exp (((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L))) :=
        (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * (C * (m : ℝ) ^ 2 * f) * C) := Real.exp_le_exp.2 hexp

end Formalism.MainNotions.BridgeLemma₂
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNum
section
namespace Formalism.MainNotions.BridgeLemma₂

private theorem pow_rpow_eq_rpow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) :
    (x ^ n) ^ z = x ^ ((n : ℝ) * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem rows_num_l {P σ h cr Γ a2 dq : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4)
    (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ) :
    (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) ≤ (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by
  have hσ0 : 0 < σ := by linarith
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have key : h ^ cr ≤ P ^ cr * σ ^ (4 * cr) := by
    calc h ^ cr ≤ (P * σ ^ 4) ^ cr := Real.rpow_le_rpow hh0 hh hcr
      _ = P ^ cr * (σ ^ 4) ^ cr := Real.mul_rpow hP0.le (pow_nonneg hσ0.le 4)
      _ = P ^ cr * σ ^ (4 * cr) := by rw [pow_rpow_eq_rpow_mul hσ0.le]; norm_num
  have hsq : (h ^ cr) ^ 2 ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul key key (Real.rpow_nonneg hh0 _) (le_trans (Real.rpow_nonneg hh0 _) key)
  have e : σ ^ (8 * cr + a2 - dq) = σ ^ (4 * cr) * σ ^ (4 * cr) * σ ^ a2 * σ ^ (-dq) := by
    rw [← Real.rpow_add hσ0, ← Real.rpow_add hσ0, ← Real.rpow_add hσ0]
    congr 1
    ring
  have hnn : 0 ≤ Γ * σ ^ a2 * σ ^ (-dq) :=
    mul_nonneg (mul_nonneg hΓ (Real.rpow_nonneg hσ0.le _)) (Real.rpow_nonneg hσ0.le _)
  calc (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) = (h ^ cr) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := by ring
    _ ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := mul_le_mul_of_nonneg_right hsq hnn
    _ = (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by rw [e]; ring

theorem rows_num_pair {P σ₁ σ₂ h₁ h₂ cr Γ a2 dq E1 F6 XiH XiP ck e l₁ l₂ : ℝ} (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (h1₁ : 1 ≤ h₁) (h1₂ : 1 ≤ h₂) (hh₁ : h₁ ≤ P * σ₁ ^ 4) (hh₂ : h₂ ≤ P * σ₂ ^ 4) (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ)
    (hE1 : 0 ≤ E1) (hF6 : 0 ≤ F6) (hXiH : 0 ≤ XiH) (hXi : XiH ≤ XiP * (σ₁ * σ₂) ^ (4 * ck))
    (hl₁ : l₁ = (h₁ ^ cr) ^ 2 * (Γ * σ₁ ^ a2) * σ₁ ^ (-dq)) (hl₂ : l₂ = (h₂ ^ cr) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq))
    (he : 4 * ck + 4 * E1 + 4 * cr + a2 / 2 - dq / 2 ≤ -e) :
    XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂) ≤
      XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hP0 : 0 < P := by linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS1 : 1 ≤ σ₁ * σ₂ := by nlinarith
  have hS0 : 0 < σ₁ * σ₂ := by linarith
  have hA : 0 ≤ (P ^ cr) ^ 2 * Γ := mul_nonneg (sq_nonneg _) hΓ
  have hb₁ : l₁ ≤ (P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq) := by
    rw [hl₁]; exact rows_num_l hP hσ₁ h1₁ hh₁ hcr hΓ
  have hb₂ : l₂ ≤ (P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [hl₂]; exact rows_num_l hP hσ₂ h1₂ hh₂ hcr hΓ
  have hl₂0 : 0 ≤ l₂ := by
    rw [hl₂]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hΓ (Real.rpow_nonneg hσ₂0.le _)))
      (Real.rpow_nonneg hσ₂0.le _)
  have hhalf : (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)
      = σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [← Real.rpow_add hS0, ← Real.mul_rpow hσ₁0.le hσ₂0.le]
    congr 1
    ring
  have hsq : Real.sqrt (l₁ * l₂) ≤ (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) := by
    have hprod : l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by
      calc l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq)) *
            ((P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq)) :=
            mul_le_mul hb₁ hb₂ hl₂0 (mul_nonneg hA (Real.rpow_nonneg hσ₁0.le _))
        _ = ((P ^ cr) ^ 2 * Γ) ^ 2 * (σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq)) := by ring
        _ = ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by rw [← hhalf]; ring
    calc Real.sqrt (l₁ * l₂)
        ≤ Real.sqrt (((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) :=
          Real.sqrt_sq (mul_nonneg hA (Real.rpow_nonneg hS0.le _))
  have hE : (h₁ * h₂) ^ E1 ≤ (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
    have hprod : h₁ * h₂ ≤ P ^ 2 * (σ₁ * σ₂) ^ 4 := by
      calc h₁ * h₂ ≤ (P * σ₁ ^ 4) * (P * σ₂ ^ 4) :=
            mul_le_mul hh₁ hh₂ (by linarith) (mul_nonneg hP0.le (pow_nonneg hσ₁0.le 4))
        _ = P ^ 2 * (σ₁ * σ₂) ^ 4 := by ring
    calc (h₁ * h₂) ^ E1 ≤ (P ^ 2 * (σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.rpow_le_rpow (mul_nonneg (by linarith) (by linarith)) hprod hE1
      _ = (P ^ 2) ^ E1 * ((σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.mul_rpow (pow_nonneg hP0.le 2) (pow_nonneg hS0.le 4)
      _ = (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
          rw [pow_rpow_eq_rpow_mul hS0.le, sq, sq, Real.mul_rpow hP0.le hP0.le]
          norm_num
  have hSck : 0 < (σ₁ * σ₂) ^ (4 * ck) := Real.rpow_pos_of_pos hS0 _
  have hXiP : 0 ≤ XiP := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hSck
    linarith
  have hC : 0 ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) :=
    mul_nonneg hXiP (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hF6) hΓ)
  calc XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂)
      ≤ (XiP * (σ₁ * σ₂) ^ (4 * ck)) * ((P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) * F6) *
          ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        refine mul_le_mul ?_ hsq (Real.sqrt_nonneg _) ?_
        · exact mul_le_mul hXi (mul_le_mul_of_nonneg_right hE hF6)
            (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by linarith) (by linarith)) _) hF6)
            (mul_nonneg hXiP hSck.le)
        · exact mul_nonneg (mul_nonneg hXiP hSck.le)
            (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0.le _)) hF6)
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          ((σ₁ * σ₂) ^ (4 * ck) * (σ₁ * σ₂) ^ (4 * E1) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        ring
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          (σ₁ * σ₂) ^ (4 * ck + 4 * E1 + (8 * cr + a2 - dq) / 2) := by
        rw [Real.rpow_add hS0, Real.rpow_add hS0]
    _ ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ * σ₂) ^ (-e) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)) hC
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
        rw [Real.mul_rpow hσ₁0.le hσ₂0.le]

end Formalism.MainNotions.BridgeLemma₂
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneA
section
namespace Formalism.MainNotions.BridgeLemma₂

theorem div_rpow_le_inv_pow {k r : ℕ} {C δ : ℝ} (hk : 1 ≤ k) (hC : 1 ≤ C) (hδ : δ ≤ 1 / 4) (hCk : C ^ 3 ≤ k) :
    (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ ((k : ℝ) ^ r)⁻¹ := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hkne : (k:ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hb0 : 0 < C / k := div_pos hC0 hk0
  have hCk' : C ≤ k := by
    nlinarith [mul_nonneg (mul_nonneg hC0.le (sub_nonneg.2 hC)) (by linarith : (0:ℝ) ≤ C + 1)]
  have hb1 : C / k ≤ 1 := by rw [div_le_iff₀ hk0]; linarith
  have he : (3:ℝ) * ((r:ℝ) / 2) ≤ 2 * (r : ℝ) * (1 - δ) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.2 hδ)]
  have hb3 : (C / k) ^ 3 ≤ ((k:ℝ) ^ 2)⁻¹ := by
    rw [div_pow, div_le_iff₀ (pow_pos hk0 3)]
    calc C ^ 3 ≤ k := hCk
      _ = ((k:ℝ) ^ 2)⁻¹ * (k:ℝ) ^ 3 := by
        rw [eq_comm, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hkne)]; ring
  have hkr : (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) = ((k:ℝ) ^ r)⁻¹ := by
    rw [Real.inv_rpow (pow_nonneg hk0.le 2)]
    congr 1
    rw [← Real.rpow_natCast (k:ℝ) 2, ← Real.rpow_mul hk0.le, ← Real.rpow_natCast (k:ℝ) r]
    congr 1; push_cast; ring
  calc (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ (C / k) ^ ((3:ℝ) * ((r:ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hb0 hb1 he
    _ = ((C / k) ^ 3) ^ ((r:ℝ) / 2) := by
        rw [Real.rpow_mul hb0.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ ≤ (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) :=
        Real.rpow_le_rpow (pow_nonneg hb0.le 3) hb3 (by positivity)
    _ = ((k:ℝ) ^ r)⁻¹ := hkr

end Formalism.MainNotions.BridgeLemma₂
end

