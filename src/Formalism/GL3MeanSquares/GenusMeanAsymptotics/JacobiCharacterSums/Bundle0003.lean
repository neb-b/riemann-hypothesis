module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.RootNorm
section
open Finset Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem rootSum (N : ℕ) (hN : 0 < N) (t : ℕ) (ht : t < N) :
    ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ t = if t = 0 then (N : ℂ) else 0 := by

  have hprim := Complex.isPrimitiveRoot_exp N (by omega)
  split_ifs with ht0
  · subst ht0
    simp
  · have hx : cexp (2 * Real.pi * I / N) ^ t ≠ 1 := hprim.pow_ne_one_of_pos_of_lt (by omega) ht
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ t = (cexp (2 * Real.pi * I / N) ^ t) ^ k := fun k => pow_right_comm _ _ _
    simp_rw [h1]
    have hxN : (cexp (2 * Real.pi * I / N) ^ t) ^ N = 1 := by rw [pow_right_comm, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq hx, hxN, sub_self, zero_div]

theorem rootNorm (N : ℕ) (_hN : 0 < N) (k : ℕ) : ‖cexp (2 * Real.pi * I / N) ^ k‖ = 1 := by

  rw [norm_pow, (Complex.isPrimitiveRoot_exp N (by omega)).norm'_eq_one (by omega), one_pow]

theorem rootPowN (N : ℕ) (hN : 0 < N) (k : ℕ) : (cexp (2 * Real.pi * I / N) ^ k) ^ N = 1 := by

  rw [pow_right_comm, (Complex.isPrimitiveRoot_exp N (by omega)).pow_eq_one, one_pow]

theorem rootAvg (N : ℕ) (j : ℕ) (hj : 1 ≤ j) (hjN : j < N) (y : ℂ) (hy : ‖y‖ ≠ 1) :
    ∑ k ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k)
      = N * (y ^ N / (1 - y ^ N)) := by

  have hN : 0 < N := by omega
  have hyN : 1 - y ^ N ≠ 0 := by
    intro h
    have h2 : y ^ N = 1 := by linear_combination -h
    have h3 : ‖y‖ ^ N = 1 := by rw [← norm_pow, h2, norm_one]
    exact hy ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h3)
  have hxk : ∀ k, 1 - y * cexp (2 * Real.pi * I / N) ^ k ≠ 0 := by
    intro k h
    have h2 : y * cexp (2 * Real.pi * I / N) ^ k = 1 := by linear_combination -h
    apply hy
    have h3 := congrArg norm h2
    rwa [norm_mul, rootNorm N hN k, mul_one, norm_one] at h3
  have hS : ∀ s : ℕ, ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ s = if s % N = 0 then (N : ℂ) else 0 := by
    intro s
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ s = (cexp (2 * Real.pi * I / N) ^ k) ^ (s % N) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod s N, pow_add, pow_mul, rootPowN N hN k, one_pow, one_mul]
    simp_rw [h1]
    rw [rootSum N hN _ (Nat.mod_lt _ hN)]
  have hterm : ∀ k, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k) =
      (∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m)) / (1 - y ^ N) := by
    intro k
    rw [div_eq_div_iff (hxk k) hyN]
    have hg := mul_neg_geom_sum (y * cexp (2 * Real.pi * I / N) ^ k) N
    have hxN : (y * cexp (2 * Real.pi * I / N) ^ k) ^ N = y ^ N := by rw [mul_pow, rootPowN N hN k, mul_one]
    rw [hxN] at hg
    have h1 : ∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m) =
        (y * cexp (2 * Real.pi * I / N) ^ k) ^ j * ∑ i ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [h1, ← hg]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hS]
  rw [Finset.sum_eq_single (N - j)]
  · rw [if_pos (by rw [Nat.add_sub_cancel' hjN.le, Nat.mod_self]), Nat.add_sub_cancel' hjN.le]
    ring
  · intro m hm hne
    rw [Finset.mem_range] at hm
    rw [if_neg, mul_zero]
    by_cases hlt : j + m < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro h
    exfalso
    simp at h
    omega

theorem ratioLim (y : ℂ) (hy : ‖y‖ ≠ 1) :
    Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (if 1 < ‖y‖ then (-1 : ℂ) else 0)) := by

  split_ifs with h
  · have hz : ‖y⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ h
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
    have h2 : Tendsto (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) atTop (𝓝 (1 / (0 - 1))) :=
      tendsto_const_nhds.div (h1.sub tendsto_const_nhds) (by norm_num)
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith
    have h3 : (fun N : ℕ => y ^ N / (1 - y ^ N)) = (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) := by
      funext N
      have hyN : y ^ N ≠ 0 := pow_ne_zero _ hy0
      rw [inv_pow, show (y ^ N)⁻¹ - 1 = (1 - y ^ N) / y ^ N by field_simp, one_div_div]
    have h4 : (-1 : ℂ) = 1 / (0 - 1) := by norm_num
    rw [h3, h4]
    exact h2
  · have hlt : ‖y‖ < 1 := lt_of_le_of_ne (not_lt.mp h) hy
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
    have h2 : Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (0 / (1 - 0))) :=
      h1.div (tendsto_const_nhds.sub h1) (by norm_num)
    rw [show (0 : ℂ) / (1 - 0) = 0 by norm_num] at h2
    exact h2

theorem avgLimit {n : ℕ} (y : Fin n → ℂ) (hy : ∀ i, ‖y i‖ ≠ 1) (j : ℕ) (hj : 1 ≤ j) (K : ℝ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ j / (1 - y i * ζ)‖ ≤ K) :
    ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) ≤ K := by

  classical
  have hbound : ∀ N : ℕ, j < N → ‖∑ i, y i ^ N / (1 - y i ^ N)‖ ≤ K := by
    intro N hjN
    have hN : 0 < N := by omega
    have h1 : ∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k) = N * ∑ i, y i ^ N / (1 - y i ^ N) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rootAvg N j hj hjN (y i) (hy i))
    have h2 : ‖∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ ≤ N * K := by
      calc _ ≤ ∑ k ∈ range N, ‖∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
            (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range N, K := Finset.sum_le_sum (fun k _ => hK _ (rootNorm N hN k))
        _ = N * K := by simp
    rw [h1, norm_mul, Complex.norm_natCast] at h2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact le_of_mul_le_mul_left h2 hNpos
  have hlim : Tendsto (fun N : ℕ => ∑ i, y i ^ N / (1 - y i ^ N)) atTop
      (𝓝 (∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0)) :=
    tendsto_finsetSum _ (fun i _ => ratioLim (y i) (hy i))
  have hle : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ ≤ K := by
    apply le_of_tendsto hlim.norm
    rw [Filter.eventually_atTop]
    exact ⟨j + 1, fun N hN => hbound N (by omega)⟩
  have hval : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ = ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, norm_mul, norm_neg,
      norm_one, mul_one, Complex.norm_natCast]
  rw [← hval]
  exact hle

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
section
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_mertens_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
  have hsub : ∑ n ∈ Icc 1 N, (Λ n : ℝ) = ∑ n ∈ Icc 0 N, (Λ n : ℝ) := by
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [mem_Icc] at hn hn'
      have h0 : n = 0 := by omega
      subst h0
      simp
  rw [hsub]
  exact h

theorem tail_mertens_nat (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction N with
  | zero => simp
  | succ M ih =>
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
    have hB := tail_mertens_psi (M + 1)
    push_cast at hB
    have hlog : 1 / ((M:ℝ) + 1 + 1) ≤ Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM1.ne']
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M:ℝ) + 1 + 1) / ((M:ℝ) + 1)) (by positivity)
      calc 1 / ((M:ℝ) + 1 + 1) = 1 - (((M:ℝ) + 1 + 1) / ((M:ℝ) + 1))⁻¹ := by
            field_simp
            ring
        _ ≤ _ := h
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 + 1 by omega)]
    push_cast
    set B := ∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ) with hBdef
    set L := (Λ (M + 1 + 1) : ℝ) with hLdef
    have key1 : B / ((M:ℝ) + 1) ≤ (B + (Real.log 4 + 4)) / ((M:ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ hM1 hM2]
      nlinarith
    have key2 : (Real.log 4 + 4) / ((M:ℝ) + 1 + 1) ≤
        (Real.log 4 + 4) * (Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog hc
    rw [add_div] at key1 ⊢
    linarith

theorem tail_mertens : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * (1 / Real.log 2 + 1),
    mul_nonneg hc (add_nonneg (one_div_nonneg.2 hl2.le) zero_le_one), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨M, hM⟩ : ∃ M, ⌊y⌋₊ = M + 1 :=
    ⟨⌊y⌋₊ - 1, by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega⟩
  rw [hM]
  have h1 := tail_mertens_nat M
  have hpsi := tail_mertens_psi (M + 1)
  push_cast at hpsi
  have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hMy : (M:ℝ) + 1 ≤ y := by
    have := Nat.floor_le hy0
    rw [hM] at this
    push_cast at this
    exact this
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogM : Real.log ((M:ℝ) + 1) ≤ Real.log y := Real.log_le_log hM1 hMy
  have hq : (∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ)) / ((M:ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hM1]
    exact hpsi
  have hone : 1 ≤ Real.log y / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  calc _ ≤ (Real.log 4 + 4) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hlogM hc
        linarith
    _ ≤ (Real.log 4 + 4) * (Real.log y / Real.log 2) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hone hc
        linarith
    _ = (Real.log 4 + 4) * (1 / Real.log 2 + 1) * Real.log y := by
        field_simp

end Formalism.HermitianLattices.Ext.BoxTail
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailNum
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  suffices h : ∀ n : ℕ,
      (x ^ n + 1) * Real.log (x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2)) / x ^ (n + 1)
        ≤ 2 * ((n : ℝ) + 3) by
    have hbound : 2 * ((398 : ℝ) + 3) = 802 := by norm_num
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, hbound] using h 398
  intro n
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ n := by positivity
  have hp1 : 1 ≤ x ^ n := one_le_pow₀ hx1
  have hA : x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2) = x ^ n * (x ^ 2 + 1) := by
    rw [pow_add]
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hsq_pos : 0 < x ^ 2 + 1 := by positivity
  have hlog_sq : Real.log (x ^ 2 + 1) ≤ 3 * Real.log x := by
    calc Real.log (x ^ 2 + 1) ≤ Real.log (x ^ 3) := Real.log_le_log hsq_pos hsq
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlog_x : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hL1 : Real.log (x ^ n * (x ^ 2 + 1)) ≤ ((n : ℝ) + 3) * x := by
    rw [Real.log_mul hp.ne' hsq_pos.ne', Real.log_pow]
    calc (n : ℝ) * Real.log x + Real.log (x ^ 2 + 1)
        ≤ (n : ℝ) * Real.log x + 3 * Real.log x := add_le_add le_rfl hlog_sq
      _ = ((n : ℝ) + 3) * Real.log x := by ring
      _ ≤ ((n : ℝ) + 3) * x := mul_le_mul_of_nonneg_left hlog_x (by positivity)
  have hxn : x ≤ x ^ (n + 1) := by
    simpa only [pow_succ, one_mul] using mul_le_mul_of_nonneg_right hp1 hx0.le
  rw [hA, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ (n + 1))]
  calc (x ^ n + 1) * Real.log (x ^ n * (x ^ 2 + 1))
      ≤ (x ^ n + 1) * (((n : ℝ) + 3) * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = ((n : ℝ) + 3) * (x ^ (n + 1) + x) := by rw [pow_succ]; ring
    _ ≤ ((n : ℝ) + 3) * (x ^ (n + 1) + x ^ (n + 1)) := by gcongr
    _ = 2 * ((n : ℝ) + 3) * x ^ (n + 1) := by ring

end Formalism.HermitianLattices.Ext.BoxTail
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TpCoeffNorm
section
open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def tp (n : ℕ) (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))

theorem tp_natDeg (n : ℕ) (z : Fin n → ℂ) : (tp n z).natDegree ≤ n := by
  unfold tp
  exact (natDegree_prod_le _ _).trans (by simp [natDegree_X_sub_C])

theorem tp_eval (n : ℕ) (z : Fin n → ℂ) (x : ℂ) : (tp n z).eval x = ∏ i, (x - z i) := by
  simp [tp, eval_prod]

theorem tp_eval_sum (n : ℕ) (z : Fin n → ℂ) (x : ℂ) :
    (tp n z).eval x = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (tp_natDeg n z)) x

theorem tp_coeff_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (a : ℕ) (ha : a ≤ n) :
    ‖(tp n z).coeff a‖ ≤ n.choose a := by
  classical
  set s : Multiset ℂ := Finset.univ.val.map z with hs
  have hcard : Multiset.card s = n := by simp [hs]
  have htp : tp n z = (s.map fun t => X - C t).prod := by
    rw [tp, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  have hprod : ∀ t : Multiset ℂ, (∀ x ∈ t, ‖x‖ ≤ 1) → ‖t.prod‖ ≤ 1 := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons x t ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (h x (Multiset.mem_cons_self x t)) (norm_nonneg _)
        (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))
  have hmem : ∀ t ∈ s, ‖t‖ ≤ 1 := by
    intro t ht
    rw [hs, Multiset.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hz i
  rw [htp, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact ha), hcard, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← Nat.choose_symm ha, Multiset.esymm]
  calc ‖((s.powersetCard (n - a)).map Multiset.prod).sum‖
      ≤ (((s.powersetCard (n - a)).map Multiset.prod).map norm).sum := norm_multiset_sum_le _
    _ = ((s.powersetCard (n - a)).map fun t => ‖t.prod‖).sum := by rw [Multiset.map_map]; rfl
    _ ≤ ((s.powersetCard (n - a)).map fun _ => (1 : ℝ)).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun t ht => hprod t fun x hx => hmem x ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx
    _ = n.choose (n - a) := by simp [Multiset.card_powersetCard, hcard]

theorem tp_sum_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ 2 ^ n := by
  calc ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ ∑ a ∈ range (n + 1), (n.choose a : ℝ) :=
        Finset.sum_le_sum fun a ha => tp_coeff_norm n z hz a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n

theorem tp_rev (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
  have h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹ := by
    rw [tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_inv_cancel₀ hζ]
    ring
  rw [h1, tp_eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [inv_pow, pow_sub₀ _ hζ ha']
  ring

theorem tp_root (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by
  rw [← tp_eval_sum, tp_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

