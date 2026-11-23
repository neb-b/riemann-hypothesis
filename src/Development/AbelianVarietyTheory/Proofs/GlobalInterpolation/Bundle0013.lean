module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIccThreeQuartersPowLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem sum_Icc_three_quarters_pow_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 3 - 3 * (3 / 4 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [pow_succ]
    linarith

theorem powerSum_weighted_ineq {ι : Type} (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι)
    (L δ x : ℝ) (hi : i₀ ∈ S) (hb : 1 ≤ b i₀) (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hz : 1 / (1 + x) ≤ ‖z i₀‖) (hS : (∑ i ∈ S, (b i : ℝ)) ≤ L)
    (hp : ∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) (J : ℕ) :
    (J : ℝ) / 4 - 7 * L ≤ 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (S.filter fun i => 1 ≤ b i)
    (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩
  obtain ⟨hi₁S, hb₁⟩ := Finset.mem_filter.1 hi₁
  set R : ℝ := ‖z i₁‖ with hR
  have h1x : 0 < 1 + x := by linarith
  have hRge : 1 / (1 + x) ≤ R := hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRinv : R⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hRpos h1x, ← one_div]; exact hRge
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  set θ : ℝ := Complex.arg (z i₁) with hθ
  obtain ⟨hF1, hF2⟩ := _root_.GlobalTheory.weighted_fejer_positivity J θ
  set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc
  set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF
  have hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w := hF1
  have hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I)) := hF2
  set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw
  have hw₁ : w i₁ = Complex.exp (θ * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z i₁)
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _
    rw [← h]
    push_cast
    rw [← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  have hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1 := by
    intro i hiS hbi
    have := hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)
    show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]
    exact this

  have hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i) := by
    have hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1) := by
      intro i hiS
      rcases Nat.eq_zero_or_pos (b i) with h0 | h0
      · simp [h0]
      · have := hF1' _ (hwn i hiS h0)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 := Finset.single_le_sum hnn hi₁S
    have hb1 : (1 : ℝ) ≤ b i₁ := by exact_mod_cast hb₁
    have h2 := hF1' _ (hwn i₁ hi₁S hb₁)
    have h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1) := by nlinarith
    have h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1)
        = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hw₁] at hF2'
    linarith

  have hex : ∑ i ∈ S, (b i : ℝ) * F (w i)
      = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) := by
    simp only [hF, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re := by
      show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _
      rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e1, e2]; ring

  have hup : ∀ j ∈ Finset.Icc 1 J,
      c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
    have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hJ1 : (0 : ℝ) < J + 1 := by positivity
    have ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
      rw [sub_nonneg, div_le_one hJ1]; linarith
    have ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
      linarith
    have hcos1 := Real.cos_le_one (j * θ)
    have hcos2 := Real.neg_one_le_cos (j * θ)
    have hc0 : 0 ≤ c j := mul_nonneg ha0 (by linarith)
    have hc2 : c j ≤ 2 := by
      show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2
      nlinarith
    have hq : R⁻¹ ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hRinv0 hRinv j
    have hq2 : (1 + x) ^ j ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hjJ
    have hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ h1x.le (by linarith) j
    have hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j := by positivity
    have s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re
        ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) :=
      (mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hq hB0)
    have s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ) := by gcongr
    have s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j) := by gcongr
    have s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j := by
      have : (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j := by rw [← div_pow]; norm_num
      rw [this]; ring
    have s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) := by positivity
    calc c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ c j * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_left s1 hc0
      _ ≤ 2 * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_right hc2 s5
      _ ≤ _ := by rw [mul_add ((1 + x) ^ j)]; linarith
  have hsum := Finset.sum_le_sum hup
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hg := sum_Icc_three_quarters_pow_le J
  have hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
  have hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by ring
  linarith

theorem powerSum_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι) (L δ x : ℝ), i₀ ∈ S → 1 ≤ b i₀ → 1 ≤ L → 0 < δ → 0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z i₀‖ → (∑ i ∈ S, (b i : ℝ)) ≤ L → (∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) → Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  refine ⟨2080, by norm_num, ?_⟩
  intro ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp
  have h := powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊
  set J : ℕ := ⌈64 * L⌉₊ with hJ
  have hJ1 : 64 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ 65 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)
    linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hP : (1 + x) ^ J ≤ Real.exp (x * J) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J
  have hP0 : 0 < (1 + x) ^ J := by positivity
  have h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J) := by nlinarith
  have h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h1 hJ0
  have h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J) := by
    have : 32 * (J : ℝ) ≤ 2080 * L := by linarith
    gcongr
  have hD : 0 < 2080 * L * δ := by positivity
  have h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J) := by
    rw [div_le_iff₀ hD]; linarith
  have h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J :=
    (Real.log_le_iff_le_exp (by positivity)).2 h4
  rw [div_le_iff₀ (by positivity)]
  have : x * J ≤ x * (2080 * L) := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumTruncConv
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZeroDetect


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.ZeroDetect.sum_trunc_conv (a f : ℕ → ℂ)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (D X : ℕ) :
    ∑ n ∈ Finset.Ioc 0 X, (∑ d ∈ n.divisors.filter (fun d => d ≤ D), a d) * f n
      = ∑ d ∈ Finset.Icc 1 D, a d * f d * ∑ m ∈ Finset.Icc 1 (X / d), f m := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 D)
    (s' := fun d => (Finset.Ioc 0 X).filter (fun n => d ∣ n))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 0 < d := (Finset.mem_Icc.1 hd).1
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun n _ => n / d) (fun m _ => d * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, hX⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, Finset.mem_Icc]
      exact ⟨hk, (Nat.le_div_iff_mul_le hd1).2 (by rw [mul_comm]; exact hX)⟩
    · intro m hm
      rw [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).1 hm.2
      rw [mul_comm]; exact this
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      exact Nat.mul_div_cancel_left m hd1
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, _⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, hf d k hd1 hk]
      ring
  · intro n d
    simp only [Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hX⟩, ⟨hdn, -⟩, hdD⟩
      exact ⟨⟨⟨h0, hX⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn h0, hdD⟩
    · rintro ⟨⟨⟨h0, hX⟩, hdn⟩, -, hdD⟩
      exact ⟨⟨h0, hX⟩, ⟨hdn, h0.ne'⟩, hdD⟩


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.ZeroDetect.sum_initial (f : ℕ → ℂ) (D : ℕ) (hD : 1 ≤ D) :
    ∑ n ∈ Finset.Ioc 0 D,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ D), (moebius d : ℤ) : ℤ) : ℂ) * f n = f 1 := by
  have hsum : ∀ n, ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  rw [Finset.sum_eq_single 1]
  · simp [Finset.filter_singleton, hD]
  · intro n hn hn1
    have hfil : n.divisors.filter (fun d => d ≤ D) = n.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      exact (Nat.divisor_le hd).trans (Finset.mem_Ioc.1 hn).2
    rw [hfil, hsum, if_neg hn1]
    simp
  · intro h
    exact absurd (Finset.mem_Ioc.2 ⟨zero_lt_one, hD⟩) h

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.ZeroDetect.rpow_bound {Q y σ : ℝ} (hQ : 1024 ≤ Q) (hy : Q ^ 6 ≤ 2 * y)
    (hσ : 11 / 12 ≤ σ) :
    y ^ (-σ) ≤ (16 * Q ^ 5)⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hQ6 : (2:ℝ) ^ 60 ≤ Q ^ 6 := by
    calc (2:ℝ) ^ 60 = 1024 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := pow_le_pow_left₀ (by norm_num) hQ 6
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have h5 : 0 < 16 * Q ^ 5 := by positivity
  have key : 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := by
    have hpow : (y ^ ((11:ℝ) / 12)) ^ 12 = y ^ 11 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have h12 : (16 * Q ^ 5) ^ 12 ≤ (y ^ ((11:ℝ) / 12)) ^ 12 := by
      rw [hpow]
      have hyQ : Q ^ 6 / 2 ≤ y := by linarith
      calc (16 * Q ^ 5) ^ 12 = 2 ^ 48 * Q ^ 60 := by ring
        _ ≤ (Q ^ 6) ^ 11 / 2 ^ 11 := by
          have : (Q ^ 6) ^ 11 = Q ^ 6 * Q ^ 60 := by ring
          rw [this]
          have hQ60 : 0 < Q ^ 60 := by positivity
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        _ = (Q ^ 6 / 2) ^ 11 := by ring
        _ ≤ y ^ 11 := pow_le_pow_left₀ (by positivity) hyQ 11
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h12
  rw [Real.rpow_neg hy0.le]
  apply inv_anti₀ h5
  calc 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := key
    _ ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_le hy1 hσ


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.ZeroDetect.zero_detect : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → q ≤ Q → ∀ ρ : ℂ,
    1 - 1 / 400 ≤ ρ.re → |ρ.im| ≤ Q → LFunction χ ρ = 0 →
    (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖ := by
  refine ⟨1024, fun Q hQ q _ χ hχ hqQ ρ hre him hL => ?_⟩
  have hσ : (11 / 12 : ℝ) ≤ ρ.re := by norm_num at hre; linarith
  have hσ0 : 0 < ρ.re := by linarith
  have hQR : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hD : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ3 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have hD2 : 2 * Q ^ 3 ≤ Q ^ 6 := by
    calc 2 * Q ^ 3 ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul_right _ hQ3
      _ = Q ^ 6 := by ring
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) * (n : ℂ) ^ (-ρ) with hfdef
  set a : ℕ → ℂ := fun d => ((moebius d : ℤ) : ℂ) with hadef
  have hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n := by
    intro m n _ _
    simp only [f, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hS : ∀ Y : ℕ, ∑ n ∈ Finset.Ioc 0 Y,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Finset.Ioc 0 Y, (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), a d) * f n := by
    intro Y
    apply Finset.sum_congr rfl
    intro n _
    simp only [a, f]
    push_cast
    ring
  have hsplit := Finset.sum_Ioc_consecutive (fun n =>
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) (Nat.zero_le (Q ^ 3)) hD
  have hinit : ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) = 1 := by
    calc _ = ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * f n :=
          Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _)
      _ = f 1 := _root_.GlobalTheory.ZeroDetect.sum_initial f (Q ^ 3) (by omega)
      _ = 1 := by simp [f]
  have hmain : ∑ n ∈ Finset.Ioc 0 (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m := by
    rw [hS]
    exact _root_.GlobalTheory.ZeroDetect.sum_trunc_conv a f hf _ _
  have hnorm : ‖ρ‖ / ρ.re ≤ 1 + 2 * Q := by
    have h1 := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos hσ0] at h1
    rw [div_le_iff₀ hσ0]
    nlinarith
  set C : ℝ := 2 * (q : ℝ) * (1 + ‖ρ‖ / ρ.re) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hCle : C ≤ 8 * (Q : ℝ) ^ 2 := by
    have h4 : 1 + ‖ρ‖ / ρ.re ≤ 4 * Q := by linarith
    calc C ≤ 2 * (Q : ℝ) * (4 * Q) := by
          apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
      _ = 8 * (Q : ℝ) ^ 2 := by ring
  have hterm : ∀ d ∈ Finset.Icc 1 (Q ^ 3),
      ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.1 hd
    have hN : 1 ≤ Q ^ 6 / d := (Nat.le_div_iff_mul_le hd1).2 (by omega)
    have hP : ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re) := by
      have := _root_.GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ ρ hσ0 (Q ^ 6 / d) hN
      rw [hL, zero_sub, norm_neg] at this
      exact this
    have ha : ‖a d‖ ≤ 1 := by
      simp only [a]
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    have hfd : ‖f d‖ ≤ (d : ℝ) ^ (-ρ.re) := by
      simp only [f]
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd1, Complex.neg_re]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hyN : Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) := by
      have h1 := Nat.div_add_mod (Q ^ 6) d
      have h2 := Nat.mod_lt (Q ^ 6) hd1
      omega
    have hy : (Q : ℝ) ^ 6 ≤ 2 * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) := by exact_mod_cast hyN
    have hrp := _root_.GlobalTheory.ZeroDetect.rpow_bound hQR hy hσ
    calc ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
        = ‖a d‖ * ‖f d‖ * ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (d : ℝ) ^ (-ρ.re) * (C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re)) := by gcongr
      _ = C * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) ^ (-ρ.re) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by gcongr
  have hsum : ‖∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
      ≤ 1 / 2 := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), C * (16 * (Q : ℝ) ^ 5)⁻¹ := Finset.sum_le_sum hterm
      _ = (Q : ℝ) ^ 3 * (C * (16 * (Q : ℝ) ^ 5)⁻¹) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          simp
      _ = C / (16 * (Q : ℝ) ^ 2) := by field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
  have hT : ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m) - 1 := by
    rw [← hmain, ← hsplit, hinit]
    ring
  rw [hT, norm_sub_rev]
  have h1 := norm_sub_norm_le (1 : ℂ)
    (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m)
  rw [norm_one] at h1
  linarith

end GlobalTheory.ZeroDetect
end

