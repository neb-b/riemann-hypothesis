module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003
public import Mathlib
public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.HDSucc
section
open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def hD (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : ℂ := ∑ a ∈ range (b + 1), φ a * x ^ (b - a)

theorem hD_succ (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : hD φ x (b + 1) = x * hD φ x b + φ (b + 1) := by
  unfold hD
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl (fun a ha => ?_)
  have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring

theorem hD_tele (φ : ℕ → ℂ) (x ζ : ℂ) (K : ℕ) :
    (1 - x * ζ) * ∑ b ∈ range (K + 1), hD φ x b * ζ ^ b =
      ∑ b ∈ range (K + 1), φ b * ζ ^ b - x * hD φ x K * ζ ^ (K + 1) := by
  induction K with
  | zero => simp [hD]; ring
  | succ K ih =>
    rw [sum_range_succ (fun b => hD φ x b * ζ ^ b) (K + 1), mul_add, ih,
      sum_range_succ (fun b => φ b * ζ ^ b) (K + 1), hD_succ]; ring

theorem Tbound (n m : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (β : ℝ)
    (hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ β) (ζ : ℂ) (hζ1 : 1 ≤ ‖ζ‖)
    (hne : ∀ i, 1 - z i * ζ ≠ 0) :
    ‖∏ i, (1 - z i * ζ)‖ * ‖∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ)‖ ≤
      ‖ζ‖ ^ (m + 1) * (n * (‖ζ‖ ^ n * (2 ^ n * β))) := by
  set φ : ℕ → ℂ := fun a => (tp n z).coeff (n - a) with hφ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ (m + 1) le_rfl (by omega))
  have hDn : ∀ x, hD φ x n = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a := by
    intro x
    unfold hD
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * x ^ a) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega]
  have hrefl : ∑ b ∈ range (n + 1), φ b * ζ ^ b =
      ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * ζ ^ (n - a)) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  have perI : ∀ i, (1 - z i * ζ) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b = ∏ l, (1 - z l * ζ) := by
    intro i
    have e1 := hD_tele φ (z i) ζ (n - 1)
    rw [show n - 1 + 1 = n by omega] at e1
    rw [e1]
    have hs := hD_succ φ (z i) (n - 1)
    rw [show n - 1 + 1 = n by omega, hDn (z i), tp_root n z i] at hs
    rw [tp_rev n z ζ hζ0, ← hrefl, sum_range_succ]
    linear_combination ζ ^ n * hs
  have perT : ∀ i, (∏ l, (1 - z l * ζ)) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
      ∑ b ∈ range n, ∑ a ∈ range (b + 1), ζ ^ (m + 1) * (ζ ^ b * (φ a * z i ^ (m + 1 + b - a))) := by
    intro i
    rw [← perI i]
    have : (1 - z i * ζ) * (∑ b ∈ range n, hD φ (z i) b * ζ ^ b) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
        (z i * ζ) ^ (m + 1) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b := by
      field_simp [hne i]
    rw [this]
    unfold hD
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl (fun b _ => sum_congr rfl (fun a ha => ?_))
    have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [show m + 1 + b - a = (m + 1) + (b - a) by omega, pow_add, mul_pow]; ring
  have key : (∏ l, (1 - z l * ζ)) * ∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ) =
      ζ ^ (m + 1) * ∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a) := by
    rw [mul_sum, sum_congr rfl (fun i _ => perT i)]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun b _ => ?_)
    rw [sum_comm]
  have hφsum : ∑ a ∈ range (n + 1), ‖φ a‖ ≤ 2 ^ n := by
    have : ∑ a ∈ range (n + 1), ‖φ a‖ = ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ := by
      rw [← Finset.sum_range_reflect (fun a => ‖(tp n z).coeff a‖) (n + 1)]
      refine sum_congr rfl (fun j hj => ?_)
      simp only [hφ]
      rw [show n + 1 - 1 - j = n - j by omega]
    rw [this]; exact tp_sum_norm n z hz
  rw [← norm_mul, key, norm_mul, norm_pow]
  gcongr
  calc ‖∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
      ≤ ∑ b ∈ range n, ‖ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ range n, ‖ζ‖ ^ n * (2 ^ n * β) := by
        refine sum_le_sum (fun b hb => ?_)
        have hbn : b < n := mem_range.mp hb
        rw [norm_mul, norm_pow]
        gcongr
        calc ‖∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
            ≤ ∑ a ∈ range (b + 1), ‖φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ range (b + 1), ‖φ a‖ * β := by
              refine sum_le_sum (fun a ha => ?_)
              have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
              rw [norm_mul]
              gcongr
              exact hβ _ (by omega) (by omega)
          _ ≤ ∑ a ∈ range (n + 1), ‖φ a‖ * β := by
              apply sum_le_sum_of_subset_of_nonneg
              · exact range_subset_range.mpr (by omega)
              · intro a _ _; positivity
          _ = (∑ a ∈ range (n + 1), ‖φ a‖) * β := by rw [sum_mul]
          _ ≤ 2 ^ n * β := by gcongr
    _ = n * (‖ζ‖ ^ n * (2 ^ n * β)) := by rw [sum_const, card_range, nsmul_eq_mul]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPage
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TwentyFiveMulSmallConstant
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

def rr (a : ℕ) : ℝ := 16 * Real.exp ((a : ℝ) + 1)
def eps (a : ℕ) : ℝ := 1 / rr a
def th (a : ℕ) : ℝ := 1 / (2 * Real.log (rr a))
def kap (a : ℕ) (D : ℝ) : ℝ := th a * eps a ^ 2 / (a * (D + 1))
def c0 (a : ℕ) : ℝ := 1 / (25 * rr a)
def E0 (a : ℕ) (D : ℝ) : ℝ := Real.exp (a * D / eps a ^ 2)
def j0 (a : ℕ) : ℝ := 1 + a / eps a ^ 2
def GG (a : ℕ) (CP cZ cS c₁ : ℝ) : ℝ :=
  (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * c₁ * Real.exp (j0 a * Real.log (rr a)) + 1 + rr a + rr a ^ 2
def K0 (a : ℕ) (D CP cZ cS c₁ : ℝ) : ℝ := E0 a D * GG a CP cZ cS c₁ / th a

theorem rr_gt (a : ℕ) : 16 < rr a := by
  unfold rr
  have h1 := Real.add_one_le_exp ((a : ℝ) + 1)
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem log_rr_pos (a : ℕ) : 0 < Real.log (rr a) :=
  Real.log_pos (by linarith [rr_gt a])

theorem th_pos (a : ℕ) : 0 < th a := by
  unfold th
  exact div_pos one_pos (mul_pos two_pos (log_rr_pos a))

theorem th_log (a : ℕ) : 2 * th a * Real.log (rr a) = 1 := by
  have hL := (log_rr_pos a).ne'
  unfold th
  have e : 2 * (1 / (2 * Real.log (rr a))) * Real.log (rr a)
      = Real.log (rr a) * (Real.log (rr a))⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hL]

private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity

theorem eps_pos (a : ℕ) : 0 < eps a := by
  unfold eps
  exact div_pos one_pos (rr_pos' a)

theorem eps_le (a : ℕ) : eps a ≤ 1 / 16 := by
  have h := (rr_gt a).le
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) h

theorem kap_pos (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : 0 < kap a D := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  unfold kap
  exact div_pos (mul_pos (th_pos a) (pow_pos (eps_pos a) 2))
    (mul_pos ha0 (by linarith))

private theorem mul_kap_div_eps_sq_eq_th_div_succ (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    (a : ℝ) * kap a D / eps a ^ 2 = th a / (D + 1) := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hi : eps a ^ 2 ≠ 0 := (pow_pos (eps_pos a) 2).ne'
  calc (a : ℝ) * kap a D / eps a ^ 2
      = th a / (D + 1) * ((a : ℝ) * (a : ℝ)⁻¹)
          * (eps a ^ 2 * (eps a ^ 2)⁻¹) := by
        have e : ∀ x h i d : ℝ, x * (h * i ^ 2 / (x * d)) / i ^ 2
            = h / d * (x * x⁻¹) * (i ^ 2 * (i ^ 2)⁻¹) := by
          intro x h i d
          ring
        unfold kap
        exact e _ _ _ _
    _ = th a / (D + 1) := by
        rw [mul_inv_cancel₀ ha0, mul_inv_cancel₀ hi, mul_one, mul_one]

private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]

theorem akapD_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    a * D * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  have e2 : (a : ℝ) * D * kap a D / eps a ^ 2
      = D * ((a : ℝ) * kap a D / eps a ^ 2) := by ring
  rw [e2, mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0]

theorem akap_le' (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : a * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  rw [mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0, mul_nonneg hq0 hD]

theorem kap_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by
  have hh := th_pos a
  have hi := eps_pos a
  have hi16 := eps_le a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hM : (1 : ℝ) ≤ a * (D + 1) := by nlinarith
  have hMne : (a : ℝ) * (D + 1) ≠ 0 := (lt_of_lt_of_le one_pos hM).ne'
  have hs : kap a D * ((a : ℝ) * (D + 1)) = th a * eps a ^ 2 := by
    unfold kap
    exact div_mul_cancel_of_ne_zero_real _ _ hMne
  have hs0 : 0 ≤ kap a D := (kap_pos a ha D hD).le
  have hi2 : eps a ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hi16 hi16 hi.le (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhi := mul_le_mul_of_nonneg_left hi2 hh.le
  have hsM := mul_le_mul_of_nonneg_left hM hs0
  nlinarith [hs, hhi, hsM]

theorem twentyFive_mul_smallConstant (a : ℕ) : 25 * c0 a = 1 / rr a := by
  unfold c0
  ring

private theorem succ_cube_le_eight_pow (j : ℕ) : (j + 1) ^ 3 ≤ 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (n + 1) ^ 3 := by ring
      _ ≤ 8 * 8 ^ n := by gcongr
      _ = 8 ^ (n + 1) := by ring

theorem final_step (a : ℕ) (E G : ℝ) (hE : 0 < E) (hG : 0 < G) (j : ℕ)
    (hj : E * G < j)
    (h : 1 / (E * (rr a / 8) ^ j) ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j) : False := by
  have hb := rr_pos' a
  have hP : 0 < (rr a / 8) ^ j := by positivity
  have hB : 0 < rr a ^ j := by positivity
  have hPB : (rr a / 8) ^ j * 8 ^ j = rr a ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) = 1 :=
    div_mul_cancel_of_ne_zero_real _ _ (mul_pos hE hP).ne'
  have h2 : G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j = G * ((j : ℝ) + 1) ^ 2 :=
    div_mul_cancel_of_ne_zero_real _ _ hB.ne'
  have h3 := mul_le_mul_of_nonneg_right h (mul_pos hE hB).le
  have h4 : (8 : ℝ) ^ j ≤ G * ((j : ℝ) + 1) ^ 2 * E := by
    calc (8 : ℝ) ^ j = 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) * 8 ^ j := by
          rw [h1, one_mul]
      _ = 1 / (E * (rr a / 8) ^ j) * (E * rr a ^ j) := by
          rw [← hPB]
          ring
      _ ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * (E * rr a ^ j) := h3
      _ = G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j * E := by ring
      _ = G * ((j : ℝ) + 1) ^ 2 * E := by rw [h2]
  have hc : ((j : ℝ) + 1) ^ 3 ≤ 8 ^ j := by exact_mod_cast succ_cube_le_eight_pow j
  have hm := mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)
  nlinarith [hm, hc, h4, sq_nonneg ((j : ℝ) + 1)]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

