module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZBlock
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one' {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]
  linarith

lemma conj_natCast_cpow_neg (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [show -(starRingEnd ℂ) z = (starRingEnd ℂ) (-z) from (map_neg _ _).symm,
    Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem blockCountOf_statement : BlockCountOf := by
  intro hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
  have hJ0 : (0 : ℝ) < J := Nat.cast_pos.mpr (by omega)
  have hs0 : s0 = 1 - 1 / 400 := rfl
  have hQ0 : (0 : ℝ) < Q := by linarith
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb
  set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv
  set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hcv : ∀ p n, ‖cv p n‖ ≤ 1 := fun p n => DirichletCharacter.norm_le_one _ _
  have hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ := by
    intro i hi
    rw [← Finset.add_sum_erase T _ hi]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1 := by
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have h1 : ‖v i n‖ ≤ 1 := by
          simp only [hv]
          rw [norm_mul]
          have h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 := by
            refine norm_cpow_neg_le_one' (hmemn n hn) ?_
            simp only [Complex.sub_re, Complex.ofReal_re]
            linarith [(hT i hi).2.2.1]
          calc ‖cv i n‖ * ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 * 1 :=
                mul_le_mul (hcv i n) h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖v i n‖ * ‖v i n‖ ≤ 1 * 1 := mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ∑ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ ∑ n ∈ Ioc U (2 * U), (1 : ℝ) :=
            Finset.sum_le_sum hone
        _ = U := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]
    have hoff : ∀ j ∈ T.erase i,
        ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3 := by
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      obtain ⟨hpi, hqi, hri1, hri2, himi, -⟩ := hT i hi
      obtain ⟨hpj, hqj, hrj1, hrj2, himj, -⟩ := hT j hjT
      set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw
      have hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) =
          ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
        simp only [hv, map_mul, conj_natCast_cpow_neg]
        rw [hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) =
            -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
        ring
      have hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0) := by
        simp [hw, Complex.conj_re]
      have hwim : w.im = (ρ i).im - (ρ j).im := by
        simp [hw, Complex.conj_im]
        ring
      have hwpos : 0 < w.re := by rw [hwre]; linarith
      have hne : i ≠ j := fun h => hji h.symm
      rw [hsum]
      refine (hPair i j hpi hpj hne w hwpos U hU).trans ?_
      have hwn : ‖w‖ ≤ 1 + 2 * Q := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        have hre : |w.re| ≤ 1 := by
          rw [abs_le, hwre]
          constructor <;> linarith
        have him : |w.im| ≤ 2 * Q := by
          rw [hwim]
          calc |(ρ i).im - (ρ j).im| ≤ |(ρ i).im| + |(ρ j).im| := abs_sub _ _
            _ ≤ 2 * Q := by linarith
        linarith
      have hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2 := by
        push_cast at hqi hqj ⊢
        rw [sq]
        exact mul_le_mul hqi hqj (by positivity) hQ0.le
      calc 2 * (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖) ≤ 2 * Q ^ 2 * (2 + 2 * Q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) (by linarith)
              (by positivity) (by positivity)
        _ ≤ 8 * Q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]
    calc ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ +
          ∑ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖
        ≤ U + (T.erase i).card * (8 * Q ^ 3) := by
          refine add_le_add hdiag ?_
          have := Finset.sum_le_card_nsmul _ _ _ hoff
          rwa [nsmul_eq_mul] at this
      _ ≤ Δ := by
          rw [hΔ]
          have hc : ((T.erase i).card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_erase_le
          nlinarith [pow_pos hQ0 3]
  have hD := hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow
  have hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i) := by
    intro i hi
    unfold blk
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
    simp only [hb, hv]
    rw [show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
    ring
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hL Y N U hU)
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hb]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2)
      ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by
        rw [hblk i hi]
        exact pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)
    rwa [nsmul_eq_mul] at this
  have hup := hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)
  have hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_add_one hU0.ne']
    norm_num
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤
      T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc 8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ))) = 8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
          ring
      _ ≤ _ := hsmall
  have key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    calc _ ≤ _ := hlow.trans hup
      _ = C * ((U : ℝ) ^ (-(197 / 200 : ℝ)) * U) +
            T.card * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) := by
          rw [hΔ]
          ring
      _ ≤ _ := by
          rw [hUU]
          linarith [hsm]
  have e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2)) := by
    field_simp
    ring
  have e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2) := by
    rw [mul_one_div]
  rw [e1, e2] at key
  have h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  calc (T.card : ℝ) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) * (8 * (J : ℝ) ^ 2) := h3
    _ = 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect
section
open Complex Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma sum_blocks (f : ℕ → ℂ) (Y : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Ioc Y (Y * 2 ^ J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (Y * 2 ^ j) (2 * (Y * 2 ^ j)), f n
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, ← sum_blocks f Y J]
    have h1 : Y ≤ Y * 2 ^ J := Nat.le_mul_of_pos_right Y (by positivity)
    have h2 : Y * 2 ^ J ≤ Y * 2 ^ (J + 1) := Nat.mul_le_mul_left Y (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show 2 * (Y * 2 ^ J) = Y * 2 ^ (J + 1) by ring]
    exact (Finset.sum_Ioc_consecutive _ h1 h2).symm

lemma mollM_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 ≤ s.re) (Y : ℕ) :
    ‖∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ Y := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ 1 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    rw [norm_mul, norm_mul]
    have hμ : ‖(((μ d : ℤ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hp : ‖(d : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) ?_
      simp only [Complex.neg_re]
      linarith
    calc ‖(((μ d : ℤ)) : ℂ)‖ * ‖χ (d : ZMod q)‖ * ‖(d : ℂ) ^ (-s)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  calc ∑ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = Y := by simp

attribute [local irreducible] q0 pY pJ pN in
theorem zero_detection : DetectOf := by
  intro hM Q hQ p hp hp1 hpQ ρ hρ hρim hL
  obtain ⟨N0, χ⟩ := p
  simp only at hp hp1 hpQ hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, q0 Q = X := ⟨_, rfl⟩
  have hXQ : Q ≤ (X : ℝ) := by rw [← hX]; unfold q0; exact Nat.le_ceil Q
  have hX20 : (20 : ℝ) ≤ X := le_trans hQ hXQ
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hs0 : s0 = 399 / 400 := by unfold s0; norm_num
  have hre0 : 0 < ρ.re := by rw [hs0] at hρ; linarith

  have hχ1 : χ ≠ 1 := by
    intro h
    have hc : χ.conductor = N0 + 1 := hp
    rw [h, DirichletCharacter.conductor_one] at hc
    omega

  have hJ8 : 8 ≤ pJ Q := by unfold pJ; omega
  have hNX : X ^ 8 ≤ pN Q := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pN pJ
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pY Q = X ^ 4 := by unfold pY; rw [hX]
  have hYN : pY Q ≤ pN Q := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pY Q := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pN Q := le_trans hY1 hYN

  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum (N0 + 1) χ hχ1 _ hB ρ hre0 (pN Q) hN1
  rw [hL, zero_sub, norm_neg] at hP

  have hMI := hM (N0 + 1) χ ρ (pY Q) (pN Q) (pY Q * pN Q) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pY Q)
  set P := ∑ n ∈ Icc 1 (pN Q), χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pY Q), (((μ d : ℤ)) : ℂ) * χ (d : ZMod (N0 + 1)) * (d : ℂ) ^ (-ρ) with hMdef
  set D := ∑ n ∈ Ioc (pY Q) (pY Q * pN Q), mco (pY Q) (pN Q) n * χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hD

  have hnum : ‖P‖ * (pY Q : ℝ) ≤ 1 / 2 := by
    have hq : ((N0 + 1 : ℕ) : ℝ) + 1 ≤ 2 * X := by
      have : ((N0 + 1 : ℕ) : ℝ) ≤ Q := hpQ
      linarith
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * X := by
      have h1 : ‖ρ‖ ≤ ρ.re + Q := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + Q / ρ.re := by
        rw [div_le_iff₀ hre0]; rw [add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : Q / ρ.re ≤ 2 * Q := by
        rw [div_le_iff₀ hre0]; rw [hs0] at hρ; nlinarith
      linarith
    have hNpos : (0 : ℝ) < pN Q := by exact_mod_cast hN1
    have hXpos : (0 : ℝ) < X := by linarith
    have hpow : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by rw [hs0] at hρ; linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pN Q : ℝ) := by exact_mod_cast hNX
    have hpow2 : 4 * (X : ℝ) ^ (7 : ℕ) ≤ ((pN Q : ℕ) : ℝ) ^ (15 / 16 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) = (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_add hXpos]
        norm_num
      have hs : (4 : ℝ) ≤ Real.sqrt X := by
        rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      calc 4 * (X : ℝ) ^ (7 : ℕ) ≤ (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
            have : (0 : ℝ) ≤ (X : ℝ) ^ (7 : ℕ) := by positivity
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs this
        _ = ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) := e.symm
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pY Q : ℝ) = (X : ℝ) ^ (4 : ℕ) := by rw [hY, Nat.cast_pow]
    have hPle : ‖P‖ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) := by
      refine hP.trans ?_
      have hpos1 : (0 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      have a1 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) ≤ 2 * (2 * X) := by linarith
      have a12 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * (2 * X) * (3 * X) :=
        mul_le_mul a1 hrho hpos2 (by positivity)
      have a3 : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := hpow.trans hinv
      calc 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 2 * (2 * X) * (3 * X) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right a12 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) :=
            mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (4 : ℕ) ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) * (X : ℝ) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 3 / X := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          rw [eq_div_iff hX0]
          field_simp
          ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ hXpos]; linarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI]
    rw [norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pY Q : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith

  have hsplit : D = ∑ j ∈ range (pJ Q), blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ := by
    rw [hD, show pN Q = 2 ^ pJ Q by unfold pN; rfl, sum_blocks]
    rfl
  by_contra hcon
  push_neg at hcon
  have hJpos : (0 : ℝ) < pJ Q := by exact_mod_cast (by omega : 0 < pJ Q)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJ Q)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJ Q), ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ‖
        < ∑ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDual
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem duality_inequality : DualIneq := by
  intro ι κ S I b v Δ hΔ hrow
  classical
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨s, hs⟩ : ∃ s : ι → ℂ, s = fun i => ∑ n ∈ I, b n * v i n := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : κ → ℂ, w = fun n => ∑ i ∈ S, (starRingEnd ℂ) (s i) * v i n := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → ι → ℂ, G = fun i j => ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) :=
    ⟨_, rfl⟩
  have hs' : ∀ i, ∑ n ∈ I, b n * v i n = s i := fun i => by rw [hs]
  have hG' : ∀ i j, ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) = G i j := fun i j => by rw [hG]
  simp_rw [hs']
  simp_rw [hG'] at hrow
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i ∈ S, ‖s i‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ n ∈ I, ‖b n‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hB]
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity

  have h1 : ((X : ℝ) : ℂ) = ∑ n ∈ I, b n * w n := by
    rw [hX, Complex.ofReal_sum]
    simp_rw [hz]
    simp only [hw, Finset.mul_sum]
    conv_lhs => enter [2, i]; rw [hs]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro i _
    rw [hs]
    ring
  have h2 : X ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by
    calc X = ‖((X : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hXnn]
      _ = ‖∑ n ∈ I, b n * w n‖ := by rw [h1]
      _ ≤ ∑ n ∈ I, ‖b n * w n‖ := norm_sum_le _ _
      _ = ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by simp_rw [norm_mul]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖b n‖) (fun n => ‖w n‖)

  have hGsym : ∀ i j, ‖G i j‖ = ‖G j i‖ := by
    intro i j
    have e : G j i = (starRingEnd ℂ) (G i j) := by
      rw [hG]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [e, Complex.norm_conj]
  have e : ((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j := by
    conv_rhs => rw [Finset.sum_comm]
    rw [Complex.ofReal_sum]
    simp_rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, hG, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hle : ∑ n ∈ I, ‖w n‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
    have hnn : (0 : ℝ) ≤ ∑ n ∈ I, ‖w n‖ ^ 2 := by positivity
    calc ∑ n ∈ I, ‖w n‖ ^ 2 = ‖((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := by rw [e]
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
          apply Finset.sum_le_sum
          intro i _
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, norm_mul, Complex.norm_conj]
  have hsplit : ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) =
      ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => ‖s j‖ ^ 2 * ‖G j i‖ / 2), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hamgm : ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ ≤ Δ * X := by
    calc ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖
        ≤ ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [← hGsym i j]
          have h0 := sq_nonneg (‖s i‖ - ‖s j‖)
          have hg := norm_nonneg (G i j)
          nlinarith
      _ = ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := hsplit
      _ = ∑ i ∈ S, ‖s i‖ ^ 2 * ∑ j ∈ S, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ‖s i‖ ^ 2 * Δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = Δ * X := by rw [hX, Finset.mul_sum]; simp_rw [mul_comm]
  have hXsq : X ^ 2 ≤ B * (Δ * X) := by
    have hY : 0 ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by positivity
    calc X ^ 2 ≤ (∑ n ∈ I, ‖b n‖ * ‖w n‖) ^ 2 := by nlinarith
      _ ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * ∑ n ∈ I, ‖w n‖ ^ 2 := h3
      _ ≤ B * (Δ * X) := by
          rw [← hB]
          exact mul_le_mul_of_nonneg_left (hle.trans hamgm) hBnn
  rcases hXnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

