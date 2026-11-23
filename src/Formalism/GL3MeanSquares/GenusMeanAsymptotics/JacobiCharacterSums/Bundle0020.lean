module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.NormUSum
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0008
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnFinishTuran
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 1000000 in
theorem deuring_heilbronn_finish_turan : DHFinish2Of := by
  intro hTur hIneq hPrime
  obtain ⟨CT, a, hCT, ha, hT2⟩ := hTur
  obtain ⟨CF, hCF, hF⟩ := hIneq
  obtain ⟨CP, hCP, hP⟩ := hPrime
  obtain ⟨cS, hcS, hE⟩ := excBound (1 / 2) (by norm_num)
  obtain ⟨cZ, hcZ, hG⟩ := DHF.region_gap
  have hD0 : 0 ≤ Real.log (max CT 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨c₁, hc₁pos, hc₁Z, hc₁20⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cZ / 4 ∧ c ≤ 1 / 20 :=
    ⟨min (cZ / 4) (1 / 20), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hrr : 16 < TuranPowerSumBounds.rr a := TuranPowerSumBounds.rr_gt a
  obtain ⟨c₂, hc₂pos, hc₂k, hc₂t, hc₂K⟩ : ∃ c : ℝ, 0 < c ∧
      c ≤ TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF) ∧
      c ≤ TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a) ∧
      c * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) ≤ cZ := by
    have hk := div_pos (TuranPowerSumBounds.kap_pos a ha _ hD0) (by positivity : (0 : ℝ) < 25 * CF)
    have ht := div_pos (TuranPowerSumBounds.th_pos a) (by positivity : (0 : ℝ) < 2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)
    have hq : (0 : ℝ) < 2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) := by positivity
    refine ⟨min (min (TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF))
      (TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)))
      (cZ / (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1))),
      lt_min (lt_min hk ht) (div_pos hcZ hq),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    rw [← le_div_iff₀ hq]
    exact min_le_right _ _
  have hc0pos : 0 < TuranPowerSumBounds.c0 a := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have : 0 < 1 / TuranPowerSumBounds.rr a := by positivity
    linarith
  have hc0 : TuranPowerSumBounds.c0 a ≤ 1 / 25 := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have h1 : 1 / TuranPowerSumBounds.rr a ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  refine ⟨TuranPowerSumBounds.c0 a, c₁, c₂, 3, hc0pos, hc₁pos, hc₂pos, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT hsq hne1 hL hβ hβ1 hρ hre hIm hne
  have hL1 : 1 ≤ Real.log ((M : ℝ) * T) := DHF.logMT_ge_one M T hM hT
  have hLpos : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hgap := hG M χ₁ χ β₁ T c₁ ρ hM hT hne1 hL hc₁pos (by linarith) hβ hρ hIm hne
  have hη : 0 < 1 - ρ.re := by
    by_contra h
    push_neg at h
    nlinarith
  have hηZ : cZ / (2 * Real.log ((M : ℝ) * T)) ≤ 1 - ρ.re := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηc0 : 1 - ρ.re ≤ TuranPowerSumBounds.c0 a := by linarith
  have hlam : 0 < 1 - β₁ := by linarith
  have hEx := hE M χ₁ β₁ hsq hne1 hL
  have hs : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hmm : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hMpos.le
  have hsqrt : (M : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(M : ℝ) := by
    rw [Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hcs : cS ≤ (1 - β₁) * √(M : ℝ) := by
    rw [hsqrt] at hEx
    have h1 : cS * (1 / √(M : ℝ)) ≤ 1 - β₁ := by linarith
    rw [mul_one_div, div_le_iff₀ hs] at h1
    exact h1
  have hℓ0 : 0 ≤ Real.log (3 * (M : ℝ)) := Real.log_nonneg (by linarith)
  have hℓpos : 0 < Real.log (3 * (M : ℝ)) := Real.log_pos (by linarith)
  have hℓL : Real.log (3 * (M : ℝ)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    have hT4 : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : 3 * (M : ℝ) ≤ ((M : ℝ) * T) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hT4 (sq_nonneg (M : ℝ))]
    calc Real.log (3 * (M : ℝ)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
          Real.log_le_log (by linarith) h3
      _ = 2 * Real.log ((M : ℝ) * T) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hℓM : Real.log (3 * (M : ℝ)) ^ 2 / (M : ℝ) ≤ 32 * (1 - β₁) / cS := by
    rw [div_le_div_iff₀ hMpos hcS]
    have hls := TuranPowerSumBounds.log_sq_bound (M : ℝ) (by linarith)
    calc Real.log (3 * (M : ℝ)) ^ 2 * cS ≤ 32 * √(M : ℝ) * cS :=
          mul_le_mul_of_nonneg_right hls hcS.le
      _ ≤ 32 * √(M : ℝ) * ((1 - β₁) * √(M : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 32 * (1 - β₁) * (M : ℝ) := by linear_combination (32 * (1 - β₁)) * hmm
  rw [div_le_iff₀ hLpos]
  by_contra hcon
  push_neg at hcon
  have hKK0 : TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁ <
      Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) := by
    by_contra h
    push_neg at h
    have h1 : c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) ≤
        c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁)])
        hc₂pos.le
    have h3 : c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) ≤ cZ / 2 := by
      have e : c₂ * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) =
          2 * (c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) := by ring
      linarith
    linarith
  have hpos : 0 < c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3) := by positivity
  have hexp : (1 - β₁) * Real.log ((M : ℝ) * T) ^ 3 =
      c₁ * Real.exp (-Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3))) := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  have hρre : (22 / 25 : ℝ) ≤ ρ.re := by linarith
  have hβ20 : (19 / 20 : ℝ) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / 20 := by
      rw [div_le_iff₀ hLpos]
      nlinarith
    linarith
  obtain ⟨N, w, hwre, hwex, hwsum, hwj⟩ := hF M χ₁ χ β₁ T (1 - ρ.re) ρ hM hT hsq hne1 hL hβ20 hβ1
    hρ hρre hIm hne hη (by linarith)
  have hβP : 1 - 1 / Real.log (3 * (M : ℝ)) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / Real.log (3 * (M : ℝ)) := by
      rw [div_le_div_iff₀ hLpos hℓpos]
      nlinarith
    linarith
  refine TuranPowerSumBounds.core2 CT a hCT ha hT2 CF CP cZ cS c₁ c₂ hCF hCP hcZ hcS hc₁pos hc₁Z hc₂pos hc₂k hc₂t
    (Real.log ((M : ℝ) * T)) (Real.log (3 * (M : ℝ))) (1 - β₁) (1 - ρ.re) (M : ℝ)
    (Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)))
    hL1 hℓ0 hℓL hlam hηZ hηc0 hcon hMpos hℓM hexp hKK0 N w hwre hwex hwsum ?_
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 := hwj (i + 1) hj
  have h2 := hP M χ₁ β₁ (1 + (1 - ρ.re)) i hM hsq hne1 hL hβP hβ1 (by linarith) (by linarith)
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have e1 : (1 + (1 - ρ.re)) - 1 = 1 - ρ.re := by ring
  rw [e1] at h2
  have hA : CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * ((i : ℝ) + 2) ^ 2 / (1 - ρ.re) ^ (i + 2) =
      CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * (((i + 1 : ℕ) : ℝ) + 1) ^ 2 /
        (1 - ρ.re) ^ (i + 1 + 1) := by
    push_cast
    ring_nf
  have hC : CP * ((i : ℝ) + 2) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) =
      CP * (((i + 1 : ℕ) : ℝ) + 1) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) := by
    push_cast
    ring_nf
  rw [hA, hC] at h2
  exact h1.trans (add_le_add (add_le_add h2 le_rfl) le_rfl)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneSubTwoCpowLower
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma one_char_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 := by
  rw [Subsingleton.elim x 1, map_one]

lemma block_pigeon (Y J' N' : ℕ) (f : ℕ → ℂ) (ρ : ℂ) (hN : N' = 2 ^ J') (hJ : 0 < J') (θ : ℝ)
    (h : θ ≤ ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖) :
    ∃ j ∈ range J', θ / (J' : ℝ) ≤ ‖blkD Y N' (Y * 2 ^ j) f ρ‖ := by
  by_contra hcon
  push Not at hcon
  have hsplit : ∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ) =
      ∑ j ∈ range J', blkD Y N' (Y * 2 ^ j) f ρ := by
    have h0 := sum_blocks (fun n => mco Y N' n * f n * (n : ℂ) ^ (-ρ)) Y J'
    rw [← hN] at h0
    exact h0
  have hJpos : (0 : ℝ) < J' := by exact_mod_cast hJ
  have hlt : ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖ < θ := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    calc ∑ j ∈ range J', ‖blkD Y N' (Y * 2 ^ j) f ρ‖
        < ∑ j ∈ range J', θ / (J' : ℝ) := sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hJ.ne') hcon
      _ = θ := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

lemma two_cpow_norm (ρ : ℂ) : ‖(2 : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - ρ)
  simpa using h

lemma one_sub_two_cpow_lower (ρ : ℂ) (hρ : ρ.re ≤ 1) : (1 - ρ.re) / 2 ≤ ‖1 - (2 : ℂ) ^ (1 - ρ)‖ := by
  have h1 : ‖(2 : ℂ) ^ (1 - ρ)‖ - ‖(1 : ℂ)‖ ≤ ‖(2 : ℂ) ^ (1 - ρ) - 1‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, two_cpow_norm, norm_one] at h1
  have h2 : Real.log 2 * (1 - ρ.re) + 1 ≤ (2 : ℝ) ^ (1 - ρ.re) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.add_one_le_exp _
  have h3 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h4 : (1 / 2 : ℝ) * (1 - ρ.re) ≤ Real.log 2 * (1 - ρ.re) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith

lemma two_cpow_norm_le (ρ : ℂ) (hρ : 0 ≤ ρ.re) : ‖(2 : ℂ) ^ (1 - ρ)‖ ≤ 2 := by
  rw [two_cpow_norm]
  calc (2 : ℝ) ^ (1 - ρ.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := Real.rpow_one 2

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_first : Detect0 := by
  obtain ⟨c₀, hc₀, hZ⟩ := zFRDirichlet
  refine ⟨c₀ / 24, by positivity, ⌈96 / c₀⌉₊, ?_⟩
  intro M _ T hT hM hq ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  rw [hX] at hq ⊢
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hTX : T ≤ X := by nlinarith
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)

  have hnot : ¬ InRegion c₀ M ρ := fun h => (hZ M 1 ρ h hL).2.1 rfl
  unfold InRegion at hnot
  push Not at hnot
  have harg1 : (1 : ℝ) < (M : ℝ) * (|ρ.im| + 2) := by
    have := abs_nonneg ρ.im
    nlinarith
  have harg2 : (M : ℝ) * (|ρ.im| + 2) ≤ (X : ℝ) ^ 2 := by
    have h1 : (M : ℝ) * (|ρ.im| + 2) ≤ (M : ℝ) * (T + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hlog2 : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log X := by
    have h := Real.log_le_log (by linarith) harg2
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hbeta : c₀ / (2 * Real.log X) < 1 - ρ.re := by
    have h1 : c₀ / (2 * Real.log X) ≤ c₀ / Real.log ((M : ℝ) * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc₀.le (Real.log_pos harg1) hlog2
    linarith
  have hbeta0 : ρ.re ≤ 1 := by
    have : 0 < c₀ / (2 * Real.log X) := by positivity
    linarith

  have hζ := principal_zeta_bound M ρ hre0 hL
  have hρ1 : ρ ≠ 1 := hL.1.resolve_left (fun h => h rfl)
  have hE := eta_partial_sums ρ hre0 hρ1 (pNd M T) hN1
  rw [hζ, mul_zero, zero_sub, norm_neg] at hE

  have hP : ∀ K : ℕ, ∑ n ∈ Icc 1 K, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Icc 1 K, (n : ℂ) ^ (-ρ) :=
    fun K => sum_congr rfl (fun n _ => by rw [one_char_apply, one_mul])
  have hMI1 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (pNd M T) (pYd M T * pNd M T)
    hY1 hYN le_rfl
  have hMI2 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (2 * pNd M T)
    (pYd M T * (2 * pNd M T)) hY1 (by omega) le_rfl
  rw [hP] at hMI1 hMI2
  have hMo := mollM_norm_le (1 : DirichletCharacter ℂ 1) ρ hre0.le (pYd M T)
  have hz2 := two_cpow_norm_le ρ hre0.le
  have hzl := one_sub_two_cpow_lower ρ hbeta0
  set z : ℂ := (2 : ℂ) ^ (1 - ρ) with hz
  set P1 := ∑ n ∈ Icc 1 (pNd M T), (n : ℂ) ^ (-ρ) with hP1
  set P2 := ∑ n ∈ Icc 1 (2 * pNd M T), (n : ℂ) ^ (-ρ) with hP2
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) *
    (1 : DirichletCharacter ℂ 1) (d : ZMod 1) * (d : ℂ) ^ (-ρ) with hMdef
  set D1 := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD1
  set D2 := ∑ n ∈ Ioc (pYd M T) (pYd M T * (2 * pNd M T)), mco (pYd M T) (2 * pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD2
  have hEY : ‖P2 - z * P1‖ * (pYd M T : ℝ) ≤ 12 / (X : ℝ) ^ 2 := by
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 4 * (1 + ‖ρ‖ / ρ.re) ≤ 12 * X := by linarith
    have hPle : ‖P2 - z * P1‖ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hE.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 4 * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 12 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P2 - z * P1‖ * (X : ℝ) ^ (3 : ℕ) ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 12 / (X : ℝ) ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
  have hsmall : 12 / (X : ℝ) ^ 2 ≤ c₀ / (8 * Real.log X) := by
    have h96 : 96 ≤ (X : ℝ) * c₀ := by
      have h := Nat.ceil_le.mp hq
      rwa [div_le_iff₀ hc₀] at h
    have hl : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hXpos).trans (by linarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hkey : 1 - z = (P2 - z * P1) * Mo - D2 + z * D1 := by
    linear_combination (-1 : ℂ) * hMI2 + z * hMI1
  have hnorm : ‖1 - z‖ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
    rw [hkey]
    calc ‖(P2 - z * P1) * Mo - D2 + z * D1‖ ≤ ‖(P2 - z * P1) * Mo - D2‖ + ‖z * D1‖ := norm_add_le _ _
      _ ≤ ‖(P2 - z * P1) * Mo‖ + ‖D2‖ + ‖z * D1‖ := by
          have := norm_sub_le ((P2 - z * P1) * Mo) D2
          linarith
      _ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
          rw [norm_mul, norm_mul]
          have a1 : ‖P2 - z * P1‖ * ‖Mo‖ ≤ ‖P2 - z * P1‖ * (pYd M T : ℝ) :=
            mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
          have a2 : ‖z‖ * ‖D1‖ ≤ 2 * ‖D1‖ := mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
          linarith
  set θ : ℝ := c₀ / (24 * Real.log X) with hθ
  have hθ0 : 0 < θ := by positivity
  have hsum : 3 * θ < ‖D2‖ + 2 * ‖D1‖ := by
    have e1 : c₀ / (2 * Real.log X) / 2 = 6 * θ := by rw [hθ]; field_simp; norm_num
    have e2 : c₀ / (8 * Real.log X) = 3 * θ := by rw [hθ]; field_simp; norm_num
    have : c₀ / (2 * Real.log X) / 2 < (1 - ρ.re) / 2 := by linarith
    linarith
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hgoal : c₀ / 24 / (((pJd M T : ℝ) + 1) * Real.log X) = θ / ((pJd M T : ℝ) + 1) := by
    rw [hθ]; field_simp
  rw [hgoal]
  by_cases hc2 : θ ≤ ‖D2‖
  · obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T + 1) (2 * pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rw [pow_succ]; ring) (by omega) θ hc2
    refine ⟨1, by simp, j, hj, ?_⟩
    rw [pow_one]
    push_cast at hjb
    exact hjb
  · have hc1 : θ ≤ ‖D1‖ := by
      push Not at hc2
      linarith
    obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T) (pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rfl) (by omega) θ hc1
    refine ⟨0, by simp, j, ?_, ?_⟩
    · rw [mem_range] at hj ⊢; omega
    rw [pow_zero, one_mul]
    refine le_trans ?_ hjb
    exact div_le_div_of_nonneg_left hθ0.le hJpos (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def cS (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ)

def cT (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) * (Real.log b : ℂ) / (b : ℂ)

def cF (N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, (∑ d ∈ n.divisors, χ (d : ZMod q)) / (n : ℂ)

def hH (k : ℕ) : ℝ := ∑ a ∈ Ioc 0 k, ((a : ℝ))⁻¹

theorem cF_eq (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by
  have hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N := by
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have h1 := Nat.le_of_dvd hn0 hdn
      have h2 := Nat.pos_of_dvd_of_pos hdn hn0
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  unfold cF hH
  simp only [Finset.sum_div]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩
      have h3 := (Nat.le_div_iff_mul_le hd0).mp h2
      rw [mul_comm]
      exact h3
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℂ) ≠ 0 := by
    have h1 := (Finset.mem_Ioc.mp ha).1
    exact_mod_cast h1.ne'
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp

theorem cF_split (N U : ℕ) (hUN : U ≤ N) :
    cF χ N = ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) +
      ∑ a ∈ Ioc 0 N, ((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) := by
  rw [cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  congr 1
  have hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔
      b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N := by
    intro b a
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hUb, hbN⟩, ha0, haN⟩
      have hb0 : 0 < b := by omega
      have h1 : a * b ≤ N := (Nat.le_div_iff_mul_le hb0).mp haN
      refine ⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩
      exact le_trans (Nat.le_mul_of_pos_right a hb0) h1
    · rintro ⟨⟨hUb, hbNa⟩, ha0, haN⟩
      have h1 : b * a ≤ N := (Nat.le_div_iff_mul_le ha0).mp hbNa
      have hb0 : 0 < b := by omega
      exact ⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0,
        (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩
  unfold hH
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

