module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0014

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperC
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl

theorem term_bound (N U b : ℕ) (hb : 1 ≤ b) (hbU : b ≤ U) (hUN : U * U ≤ N) :
    |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)| ≤ 2 * b / N := by
  have hbpos : 0 < b := by omega
  have hbb : b * b ≤ N := le_trans (Nat.mul_le_mul hbU hbU) hUN
  have hk1 : 1 ≤ N / b := by
    rw [Nat.le_div_iff_mul_le hbpos]
    nlinarith
  have hdm := Nat.div_add_mod N b
  have hml := Nat.mod_lt N hbpos
  have hkb : N / b * b ≤ N := Nat.div_mul_le_self N b
  have hNlt : N < (N / b + 1) * b := by nlinarith
  have hk0 : N / b ≠ 0 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hkR : (1 : ℝ) ≤ ((N / b : ℕ) : ℝ) := by exact_mod_cast hk1
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkbR : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast hkb
  have hNltR : (N : ℝ) < (((N / b : ℕ) : ℝ) + 1) * b := by exact_mod_cast hNlt
  have hHk : hH (N / b) = ((harmonic (N / b) : ℚ) : ℝ) := hH_eq_harmonic' (N / b)
  have hA1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N / b)
  have hA2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (N / b)
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hk0, if_false] at hA1 hA2
  rw [← hHk] at hA1 hA2
  set K : ℝ := ((N / b : ℕ) : ℝ) with hK
  have hlog1 : Real.log (K + 1) - Real.log K ≤ 1 / K := by
    rw [← Real.log_div (by positivity) (by positivity), add_div, div_self (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / K by positivity)
    linarith
  have hlogB1 : Real.log K + Real.log b - Real.log N ≤ 0 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (by positivity) hkbR]
  have hlogB2 : -(1 / K) ≤ Real.log K + Real.log b - Real.log N := by
    have h1 : Real.log N < Real.log ((K + 1) * b) := Real.log_lt_log hN0 hNltR
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hfin : 1 / K ≤ 2 * b / N := by
    rw [le_div_iff₀ hN0, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem cF_main (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by
  have hUle : U ≤ N := le_trans (Nat.le_mul_of_pos_left U (by omega)) hUN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  rw [cF_split χ N U hUle]
  have hX : (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U) =
      ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) *
        (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ) := by
    unfold cS cT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [hX]
  have hre : ∀ A B C : ℂ, A + B - C = (A - C) + B := fun A B C => by ring
  rw [hre, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Ioc 0 U, ‖χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) - χ (b : ZMod q) / (b : ℂ) *
          (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ)‖
        ≤ ∑ b ∈ Ioc 0 U, 2 / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
          rw [← mul_sub, norm_mul, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast]
          have h1 := term_bound N U b hb.1 hb.2 hUN
          have h2 : ‖χ (b : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          calc ‖χ (b : ZMod q)‖ / b * |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)|
              ≤ 1 / b * (2 * b / N) := by gcongr
            _ = 2 / N := by field_simp
      _ = 2 * U / N := by simp; ring
  · have htail : ∀ a ∈ Ioc 0 N, ‖∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖ ≤ 8 * ((q : ℝ) + 1) / U := by
      intro a ha
      by_cases hM : N / a ≤ U
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at hM
        have hsplit : ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) = cS χ (N / a) - cS χ U := by
          unfold cS
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hM.le]
          ring
        rw [hsplit]
        have h1 := cS_approx χ hχ U hU
        have h2 := cS_approx χ hχ (N / a) (by omega)
        have hMR : (U : ℝ) ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hM.le
        have h3 : 4 * ((q : ℝ) + 1) / ((N / a : ℕ) : ℝ) ≤ 4 * ((q : ℝ) + 1) / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hMR
        calc ‖cS χ (N / a) - cS χ U‖ = ‖(DirichletCharacter.LFunction χ 1 - cS χ U) -
              (DirichletCharacter.LFunction χ 1 - cS χ (N / a))‖ := by
              congr 1
              ring
          _ ≤ ‖DirichletCharacter.LFunction χ 1 - cS χ U‖ +
              ‖DirichletCharacter.LFunction χ 1 - cS χ (N / a)‖ := norm_sub_le _ _
          _ ≤ 4 * ((q : ℝ) + 1) / U + 4 * ((q : ℝ) + 1) / U := add_le_add h1 (h2.trans h3)
          _ = 8 * ((q : ℝ) + 1) / U := by ring
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, ‖((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (8 * ((q : ℝ) + 1) / U) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (htail a ha) (by positivity)
      _ = hH N * (8 * ((q : ℝ) + 1) / U) := by rw [hH, Finset.sum_mul]
      _ ≤ (1 + Real.log N) * (8 * ((q : ℝ) + 1) / U) := by
          have hh : hH N ≤ 1 + Real.log N := by
            rw [hH_eq_harmonic']
            exact harmonic_le_one_add_log N
          exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by ring

theorem cF_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N))‖ ≤
      26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by
  have hU : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hUN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hU
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNR
  have hsq : √(N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity)
      (show (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) by exact_mod_cast hlt)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hsq2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have h := Real.sqrt_le_sqrt (show ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) ≤ N by exact_mod_cast hUN)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hc : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
  have h1 := cF_main χ hχ N (Nat.sqrt N) hU hUN
  have h2 := cS_approx χ hχ (Nat.sqrt N) hU
  have hdec : cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N)) =
      (cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) - cT χ (Nat.sqrt N))) +
        ((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1) := by
    ring
  rw [hdec]
  have hw : 1 / (Nat.sqrt N : ℝ) ≤ 2 * (1 / √(N : ℝ)) := by
    have h := one_div_le_one_div_of_le hs0 (show √(N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) by linarith)
    calc 1 / (Nat.sqrt N : ℝ) = 2 * (1 / (2 * (Nat.sqrt N : ℝ))) := by field_simp
      _ ≤ 2 * (1 / √(N : ℝ)) := by linarith
  have hv : (Nat.sqrt N : ℝ) / N ≤ 1 / √(N : ℝ) := by
    calc (Nat.sqrt N : ℝ) / N = (Nat.sqrt N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
          rw [Real.mul_self_sqrt hNR.le]
      _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by gcongr
      _ = 1 / √(N : ℝ) := by field_simp
  calc _ ≤ ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) -
          cT χ (Nat.sqrt N))‖ + ‖((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1)‖ := norm_add_le _ _
    _ ≤ (2 * (Nat.sqrt N : ℝ) / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / (Nat.sqrt N : ℝ)) +
          (Real.log N + Real.eulerMascheroniConstant) * (4 * ((q : ℝ) + 1) / (Nat.sqrt N : ℝ)) := by
        refine add_le_add h1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h2 hc
    _ = 2 * ((Nat.sqrt N : ℝ) / N) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (1 / (Nat.sqrt N : ℝ)) := by
        ring
    _ ≤ 2 * (1 / √(N : ℝ)) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (2 * (1 / √(N : ℝ))) := by
        gcongr
    _ ≤ 26 * ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) := by
        have hZ : 0 ≤ 1 / √(N : ℝ) := by positivity
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have a3 : ((q : ℝ) + 1) * (1 / √(N : ℝ)) * Real.eulerMascheroniConstant ≤
            ((q : ℝ) + 1) * (1 / √(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hγ1 (by positivity)
        have a4 : 1 * (1 / √(N : ℝ)) ≤ ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ
        nlinarith
    _ = 26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqF
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem deuring_heilbronn_inequality : DHIneqFOf := by
  intro hPos hLoc hDom
  obtain ⟨CL, hCL, hL⟩ := hLoc
  refine ⟨8 * CL + 1, by positivity, ?_⟩
  intro M _ χ₁ χ β₁ T η ρ hM hT hχ₁2 hχ₁1 hβ hβ1 hβ2 hρ hρre hρim hne hη hη2
  have hlog0 : Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) :=
    logMulAbsAddTwoLeTwoMulLog M T 0 hM hT (by rw [abs_zero]; linarith)
  have hlogγ := logMulAbsAddTwoLeTwoMulLog M T ρ.im hM hT hρim
  have hlog1 := dhLogOne M T hM hT
  obtain ⟨Z1, m1, hZ1, hm1, hr1, hN1, hE1⟩ := hL M 1 0 hM
  obtain ⟨Z2, m2, hZ2, hm2, hr2, hN2, hE2⟩ := hL M χ₁ 0 hM
  obtain ⟨Z3, m3, hZ3, hm3, hr3, hN3, hE3⟩ := hL M χ ρ.im hM
  obtain ⟨Z4, m4, hZ4, hm4, hr4, hN4, hE4⟩ := hL M (χ * χ₁) ρ.im hM
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) + ρ.im * I := ⟨_, rfl⟩
  have hs₀' : s₀ = ((1 + η : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hs₀]; simp
  have hs₀re : s₀.re = 1 + η := by rw [hs₀]; simp
  have hs₁re : s₁.re = 1 + η := by rw [hs₁]; simp
  have hd₀ : ‖s₀ - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₀, show ((1 + η : ℝ) : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hd₁ : ‖s₁ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₁, show ((1 + η : ℝ) : ℂ) + ρ.im * I - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h1s₀ : 1 < s₀.re := by rw [hs₀re]; linarith
  have h1s₁ : 1 < s₁.re := by rw [hs₁re]; linarith
  have hβZ : (β₁ : ℂ) ∈ Z2 := by
    refine (hZ2 β₁).2 ⟨?_, Or.inl hχ₁1, hβ⟩
    rw [show (β₁ : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β₁ - 26 / 25 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hρZ : ρ ∈ Z3 := by
    refine (hZ3 ρ).2 ⟨?_, hρ⟩
    rw [show ρ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((ρ.re - 26 / 25 : ℝ) : ℂ) by
        apply Complex.ext <;> simp,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hρ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hρ.1 (le_of_not_gt h) hρ.2
    constructor <;> linarith
  have hb2 : s₀ - β₁ ∈ dhFam Z2 m2 s₀ := dhFam_mem _ _ _ _ hβZ (hm2 _ hβZ)
  have hb3 : χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 → s₁ - β₁ ∈ dhFam Z3 m3 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm3 _ h.2)
  have hb4 : χ = 1 ∧ (β₁ : ℂ) ∈ Z4 → s₁ - β₁ ∈ dhFam Z4 m4 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm4 _ h.2)
  have hl0 : 0 ≤ Real.log ((M : ℝ) * T) := by linarith

  have big : ∀ k : ℕ, (((dhFam Z1 m1 s₀ + (dhFam Z2 m2 s₀).erase (s₀ - β₁)
      + (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
      + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁)).map
        (fun x : ℂ => 1 / x ^ (k + 1))).sum).re ≤
      2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) + (8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1))
        + 8 * 0 + Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
    intro k
    have key := dhAssemble (dhFam Z1 m1 s₀) (dhFam Z2 m2 s₀) (dhFam Z3 m3 s₁) (dhFam Z4 m4 s₁)
      (s₀ - β₁) (s₁ - β₁) (s₁ - β₁) _ _ hb2 hb3 hb4 (fun x : ℂ => 1 / x ^ (k + 1))
    rw [dhFamPow, dhFamPow, dhFamPow, dhFamPow] at key
    rw [key]
    have l1 := dhReBound _ _ _ _ (hE1 k s₀ h1s₀ hd₀)
    have l2 := dhReBound _ _ _ _ (hE2 k s₀ h1s₀ hd₀)
    have l3 := dhReBound _ _ _ _ (hE3 k s₁ h1s₁ hd₁)
    have l4 := dhReBound _ _ _ _ (hE4 k s₁ h1s₁ hd₁)
    rw [if_pos rfl] at l1
    rw [if_neg hχ₁1, Complex.zero_re] at l2
    have hp := hPos M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁, ← hs₀] at hp
    have hA : 0 ≤ ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ₁) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s₁).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (χ * χ₁)) s₁).re := by
      have e : ∀ a b c d : ℂ, ((-1 : ℂ) ^ k / (k.factorial : ℂ) * a).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * b).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * c).re + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * d).re
          = ((k.factorial : ℝ))⁻¹ * ((-1 : ℂ) ^ k * (a + b + c + d)).re := by
        intro a b c d
        rw [← Complex.re_ofReal_mul]
        simp only [← Complex.add_re]
        congr 1
        push_cast
        ring
      rw [e]
      exact mul_nonneg (by positivity) hp
    have hpair := dhPair η 0 β₁ hη hβ2 k s₀ hs₀'
    have hshift : ((if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)).re
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine le_trans (Complex.re_le_norm _) ?_
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    simp only [Complex.add_re, Complex.sub_re] at hpair hshift ⊢
    have ee0 : CL * Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog0 hCL.le) (by positivity)
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have t1 := add_le_add (add_le_add (add_le_add l1 l2) l3) l4
    have t2 : (8 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := le_trans h8 h25
    have t3 : CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k ≤ 2 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
      linarith
    exact dhFinalArith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 hA hpair hshift ee0 eeγ t3 t2 le_rfl

  obtain ⟨N, w, hw⟩ := dhFlat
    ((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
    + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁))
  refine ⟨N, w, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    have hx : w i ∈ Finset.univ.val.map w := Multiset.mem_map_of_mem w (Finset.mem_univ i)
    rw [hw] at hx
    rcases Multiset.mem_add.1 hx with h | h
    · exact dhFam_re _ _ _ _ _ hr3 hs₁re (dhMemIte _ _ _ _ h)
    · exact dhFam_re _ _ _ _ _ hr4 hs₁re (dhMemIte _ _ _ _ h)
  ·
    have hx₀ : s₁ - ρ = ((η + (1 - ρ.re) : ℝ) : ℂ) := by
      rw [hs₁]; apply Complex.ext <;> simp; ring
    have hm : s₁ - ρ ∈ dhFam Z3 m3 s₁ := dhFam_mem _ _ _ _ hρZ (hm3 _ hρZ)
    have hm' : s₁ - ρ ∈ (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) := by
      split_ifs with hc
      · rw [Multiset.mem_erase_of_ne]
        · exact hm
        · intro h'
          apply hne
          rw [hc.1, sub_right_inj.1 h']
      · exact hm
    have hS : s₁ - ρ ∈ Finset.univ.val.map w := by
      rw [hw]
      exact Multiset.mem_add.2 (Or.inl hm')
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hS
    exact ⟨i, hi.trans hx₀⟩
  ·
    have e1 : ∑ i, 1 / w i = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x)).sum := dhFlat_sum w _ hw (fun x : ℂ => 1 / x)
    rw [e1]
    have hb := big 0
    simp only [zero_add, pow_one, Nat.cast_zero] at hb
    rw [Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.sum_add, Multiset.sum_add,
      Multiset.sum_add, Complex.add_re, Complex.add_re, Complex.add_re] at hb
    rw [Multiset.map_add (f := _), Multiset.sum_add, Complex.add_re]
    have n1 := dhfReNonneg (dhFam Z1 m1 s₀) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr1 hs₀re hx; linarith)
    have n2 := dhfReNonneg ((dhFam Z2 m2 s₀).erase (s₀ - β₁)) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr2 hs₀re (Multiset.mem_of_mem_erase hx); linarith)
    have hl := mul_nonneg hCL.le hl0
    have q1 : 2 * (1 * (1 - β₁) / η ^ 2) = 2 * (1 - β₁) / η ^ 2 := by ring
    have q2 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 =
        8 * (CL * Real.log ((M : ℝ) * T) * 25) + 8 * 0 + Real.log ((M : ℝ) * T) * 25 := by ring
    rw [q2, ← q1]
    linarith
  ·
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have e1 : ∑ i, 1 / (w i) ^ (k + 1) = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x ^ (k + 1))).sum :=
      dhFlat_sum w _ hw (fun x : ℂ => 1 / x ^ (k + 1))
    rw [e1, Multiset.map_add (f := _), Multiset.sum_add, dhfEraseSum Z3 m3 s₁ (s₁ - β₁) _ hb3 k,
      dhfEraseSum Z4 m4 s₁ (s₁ - β₁) _ hb4 k]
    have hdom := hDom M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁] at hdom
    have hP : ‖(if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)‖
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    have hm := dhfNormArith _ _ _ _ _ _ _ _ _ _ k _ _ _ _ (hE3 k s₁ h1s₁ hd₁) (hE4 k s₁ h1s₁ hd₁)
      rfl rfl hdom hP
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have hX0 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
    have eG : 2 * ((k + 1 : ℕ) : ℝ) * (1 - β₁) / η ^ (k + 1 + 1) =
        2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) := by push_cast; ring
    have t4 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) =
        8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) + Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by ring
    rw [eG, t4]
    have hCL0 : 0 ≤ CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by positivity
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

