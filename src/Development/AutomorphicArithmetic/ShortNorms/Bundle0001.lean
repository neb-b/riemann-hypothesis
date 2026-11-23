module

public import Development.AutomorphicArithmetic.ShortNorms.ShortNorm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ShortNorms.ExistsThreePrimesOneModLeRpow
section
open GlobalTheory.Mem.An

namespace UpperTheory.T3

private theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

theorem exists_three_primes_one_mod_le_rpow :
    SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
      p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  intro hS
  obtain ⟨A, hA1, hA⟩ := hS
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAA : A ≤ A * A := by nlinarith
  have hAAA : 0 ≤ A * A * A := by positivity
  refine ⟨(1 + (2 * A + (2 * A + 2) * A)) * A, by nlinarith, ?_⟩
  intro N hN
  have hx : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ q : ℕ, q.Prime ∧ q % M = 1 ∧ (q : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hle
    obtain ⟨q, hq, hqm, hqle⟩ := hA M hM
    refine ⟨q, hq, hqm, le_trans hqle ?_⟩
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 (by omega) (by
    push_cast
    rw [Real.rpow_two]
    nlinarith)
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨p', hp', hp'm, hp'le⟩ := key (p * (15 * N)) (2 * A + 2)
    (by
      have := Nat.mul_le_mul hp.two_le (show 1 ≤ 15 * N by omega)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_two]
      exact mul_le_mul hple (by nlinarith) (by positivity) (by positivity))
  obtain ⟨q0, hq0, hq0m, hq0le⟩ := key (N * (p * p')) (1 + (2 * A + (2 * A + 2) * A))
    (by
      have := Nat.mul_le_mul (show 2 ≤ N by omega) (Nat.mul_pos hp.pos hp'.pos)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hple hp'le (Nat.cast_nonneg _) (by positivity)) hx0.le)
  have hp'p : p' % p = 1 := mod_eq_one_of_mod_mul hp'm hp1
  have hp'15 : p' % (15 * N) = 1 :=
    mod_eq_one_of_mod_mul (K := p) (by rw [Nat.mul_comm]; exact hp'm) (by omega)
  have hq0N : q0 % N = 1 := mod_eq_one_of_mod_mul hq0m (by omega)
  have hq0p : q0 % p = 1 :=
    mod_eq_one_of_mod_mul (K := p' * N) (by rw [show p * (p' * N) = N * (p * p') by ring]; exact hq0m) hp1
  have hq0p' : q0 % p' = 1 :=
    mod_eq_one_of_mod_mul (K := p * N) (by rw [show p' * (p * N) = N * (p * p') by ring]; exact hq0m) hp'.one_lt
  refine ⟨p, p', q0, hp, hp', hq0, ?_, ?_, ?_, hpm, hp'15, hq0N, ?_, ?_, hq0le⟩
  · intro h
    rw [← h, Nat.mod_self] at hp'p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p'
    omega
  · exact le_trans hple (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))
  · exact le_trans hp'le (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))

end UpperTheory.T3
end

-- bundled from Development.AutomorphicArithmetic.ShortNorms.levelPrimeN
section
open GlobalTheory.Mem.An

namespace UpperTheory.T3


open Filter in
private theorem ev_log_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (A D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, A + D * Real.log x ≤ k * x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (show (0:ℝ) < k / (2 * (|D| + 1)) by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * |A| / k)
  filter_upwards [h1, h2, eventually_gt_atTop (0:ℝ)] with x hx1 hx2 hx3
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx3 a
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxa] at hx1
  have hD1 : 0 < |D| + 1 := by positivity
  have e1 : D * Real.log x ≤ |D| * |Real.log x| := by
    calc D * Real.log x ≤ |D * Real.log x| := le_abs_self _
      _ = |D| * |Real.log x| := abs_mul _ _
  have e2 : |D| * |Real.log x| ≤ |D| * (k / (2 * (|D| + 1)) * x ^ a) :=
    mul_le_mul_of_nonneg_left hx1 (abs_nonneg D)
  have e3 : |D| * (k / (2 * (|D| + 1)) * x ^ a) ≤ k / 2 * x ^ a := by
    have q : |D| * (k / (2 * (|D| + 1)) * x ^ a) = (|D| / (|D| + 1)) * (k / 2 * x ^ a) := by
      field_simp
    have r : |D| / (|D| + 1) ≤ 1 := by rw [div_le_one hD1]; linarith
    have s : 0 ≤ k / 2 * x ^ a := by positivity
    rw [q]
    nlinarith
  have e4 : A ≤ k / 2 * x ^ a := by
    have t1 : 2 * |A| / k * k = 2 * |A| := div_mul_cancel₀ _ hk.ne'
    have t2 := mul_le_mul_of_nonneg_right hx2 hk.le
    nlinarith [le_abs_self A]
  linarith

set_option maxHeartbeats 800000 in
theorem levelPrimeN :
    ShortNorm → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ cs CY : ℝ, 0 < cs → 0 < CY → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d g₁ g₂ m : ℕ,
      ModAt x eps N d → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m →
      ∀ V Ts : ℝ, 1 ≤ V → V ≤ x ^ (12 : ℝ) → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / V) * Ts ∧ NormOne d (N * (g₁ * g₂) ^ 2) T := by
  intro hSN eps heps heps1 cs CY hcs hCY
  unfold ShortNorm at hSN
  obtain ⟨A, c, c', hA, hc, hc', hmain⟩ := hSN
  have hK0 : 0 < c * Real.sqrt cs := mul_pos hc (Real.sqrt_pos.mpr hcs)
  have hK3 : 0 < c * Real.sqrt cs / 3 := by linarith
  have E1 := ev_log_le (a := 1 / 6 + eps / 2) (k := c * Real.sqrt cs) (by linarith) hK0 0 12 (by norm_num)
  have E2 := ev_log_le (a := (1:ℝ) / 12) (k := 1) (by norm_num) one_pos 0 1 one_pos
  have E3 := ev_log_le (a := 3 * eps / 10) (k := c * Real.sqrt cs / 3) (by linarith) hK3 9 1 one_pos
  have E4 := ev_log_le (a := 1 / 6 - eps / 2) (k := c * Real.sqrt cs / 3) (by linarith) hK3 (8 * CY) 1 one_pos
  have E5 := ev_log_le (a := 1 / 6 + eps / 2) (k := c * Real.sqrt cs / 3) (by linarith) hK3 (Real.log 4) 1 one_pos
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (E1.and (E2.and (E3.and (E4.and (E5.and (Filter.eventually_ge_atTop (1:ℝ)))))))
  refine ⟨x₀, fun x hx N d g₁ g₂ m hMod hg1 hg2 hlg1 hlg2 hm V Ts hV1 hVx hTs hlogT => ?_⟩
  obtain ⟨F1, F2, F3, F4, F5, hx1⟩ := hx₀ x hx
  unfold ModAt at hMod
  obtain ⟨hdp, hd4, hd100, hN0, hdN, hlogN⟩ := hMod
  have hxpos : 0 < x := by linarith
  have hV0 : 0 < V := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have rp : ∀ a b : ℝ, x ^ a * x ^ b = x ^ (a + b) := fun a b => (Real.rpow_add hxpos a b).symm
  have hx13 : 0 < x ^ ((1:ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
  have hm0 : (0:ℝ) < m := lt_of_lt_of_le hx13 hm
  have hxe : 0 < x ^ eps := Real.rpow_pos_of_pos hxpos _
  have hlogT0 : 0 < Real.log Ts := lt_of_lt_of_le (mul_pos (mul_pos hcs hm0) hxe) hlogT
  have hTs1 : 1 < Ts := by
    by_contra hh
    push_neg at hh
    have := Real.log_nonpos hTs.le hh
    linarith
  have hsq : Real.sqrt cs * x ^ (1 / 6 + eps / 2) ≤ Real.sqrt (Real.log Ts) := by
    rw [Real.le_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hxpos _).le) hlogT0.le]
    have e : (Real.sqrt cs * x ^ (1 / 6 + eps / 2)) ^ 2 = cs * (x ^ ((1:ℝ) / 3) * x ^ eps) := by
      rw [mul_pow, Real.sq_sqrt hcs.le, sq, rp, rp]
      congr 2
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_left hm (mul_pos hcs hxe).le
    linarith
  have hKs : c * Real.sqrt cs * x ^ (1 / 6 + eps / 2) ≤ c * Real.sqrt (Real.log Ts) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsq hc.le
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hN0' : (0:ℝ) < N := by exact_mod_cast hN0
  have hg10 : (0:ℝ) < g₁ := by exact_mod_cast (show 0 < g₁ by omega)
  have hg20 : (0:ℝ) < g₂ := by exact_mod_cast (show 0 < g₂ by omega)
  have hdN' := Nat.le_of_dvd hN0 hdN
  have hdleN : (d:ℝ) ≤ N := by exact_mod_cast hdN'
  have hlogd : Real.log d ≤ Real.log N := Real.log_le_log hd0 hdleN
  have hg0 : 0 < g₁ * g₂ := Nat.mul_pos (by omega) (by omega)
  have hsq1 : 1 ≤ (g₁ * g₂) ^ 2 := Nat.one_le_pow _ _ hg0
  have hM3 : 3 ≤ N * (g₁ * g₂) ^ 2 := by nlinarith
  have hM : Real.log (4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2)
      = Real.log 4 + Real.log d + 2 * (Real.log N + 2 * Real.log g₁ + 2 * Real.log g₂) := by
    have h4 : (4:ℝ) ≠ 0 := by norm_num
    push_cast
    rw [Real.log_mul (mul_ne_zero h4 hd0.ne')
      (pow_ne_zero _ (mul_ne_zero hN0'.ne' (pow_ne_zero _ (mul_ne_zero hg10.ne' hg20.ne'))))]
    rw [Real.log_mul h4 hd0.ne', Real.log_pow, Real.log_mul hN0'.ne' (pow_ne_zero _ (mul_ne_zero hg10.ne' hg20.ne')),
      Real.log_pow, Real.log_mul hg10.ne' hg20.ne']
    push_cast
    ring
  have hxe5 : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hxpos _
  have hx12 : 0 < x ^ ((1:ℝ) / 12) := Real.rpow_pos_of_pos hxpos _
  have hx6 : 0 < x ^ ((1:ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
  have q1 : Real.log x ^ 2 ≤ x ^ ((1:ℝ) / 6) := by
    have a1 : Real.log x ≤ x ^ ((1:ℝ) / 12) := by linarith
    rw [sq]
    calc Real.log x * Real.log x ≤ x ^ ((1:ℝ) / 12) * x ^ ((1:ℝ) / 12) := mul_le_mul a1 a1 hlogx hx12.le
      _ = x ^ ((1:ℝ) / 6) := by rw [rp]; norm_num
  have q3 : x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ (eps / 5) * x ^ ((1:ℝ) / 6) :=
    mul_le_mul_of_nonneg_left q1 hxe5.le
  have P0 : 0 < x ^ (eps / 5) * x ^ ((1:ℝ) / 6) := mul_pos hxe5 hx6
  have f3 : 9 ≤ c * Real.sqrt cs / 3 * x ^ (3 * eps / 10) := by linarith
  have q4 : 9 * (x ^ (eps / 5) * x ^ ((1:ℝ) / 6)) ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by
    have e : x ^ (1 / 6 + eps / 2) = x ^ (3 * eps / 10) * (x ^ (eps / 5) * x ^ ((1:ℝ) / 6)) := by
      rw [rp, rp]
      congr 1
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_right f3 P0.le
    linarith
  have f4 : 8 * CY ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 - eps / 2) := by linarith
  have q5 : 8 * CY * x ^ eps ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by
    have e : x ^ (1 / 6 + eps / 2) = x ^ (1 / 6 - eps / 2) * x ^ eps := by
      rw [rp]
      congr 1
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_right f4 hxe.le
    linarith
  have f5 : Real.log 4 ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by linarith
  have hlogbound : Real.log (4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log Ts) := by
    rw [hM]
    linarith
  have hVle : Real.log V ≤ c * Real.sqrt (Real.log Ts) := by
    have t : Real.log V ≤ Real.log (x ^ (12:ℝ)) := Real.log_le_log hV0 hVx
    rw [Real.log_rpow hxpos] at t
    linarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log Ts)) ≤ 1 / V := by
    rw [neg_mul, Real.exp_neg, one_div]
    apply inv_anti₀ hV0
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ ≤ _ := Real.exp_le_exp.mpr hVle
  have hh1 : 1 / V ≤ 1 := by rw [div_le_one hV0]; exact hV1
  have key := hmain d (N * (g₁ * g₂) ^ 2) Ts (1 / V) hdp hd4 hd100 hM3 hTs1.le hlogbound hexp hh1
  have hMpos : (0:ℝ) < ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hM3
  have hbase : (0:ℝ) < 4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hd0) (pow_pos hMpos 2)
  have hpos : (0:ℝ) < c' * (1 / V) * Ts / ((4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ^ A * Real.log Ts) :=
    div_pos (mul_pos (mul_pos hc' (one_div_pos.mpr hV0)) hTs)
      (mul_pos (Real.rpow_pos_of_pos hbase A) hlogT0)
  have hcard : 0 < (normPrimes d (N * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / V))).card := by
    exact_mod_cast lt_of_lt_of_le hpos key
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hlo, hhi⟩, hpp, hno⟩ := hp
  have hY : 0 ≤ Ts * (1 + 1 / V) := mul_nonneg hTs.le (by have := one_div_pos.mpr hV0; linarith)
  refine ⟨p, hpp, Nat.lt_of_floor_lt hlo, ?_, hno⟩
  have t := (Nat.le_floor_iff hY).mp hhi
  rw [mul_comm]
  exact t

end UpperTheory.T3
end

-- bundled from Development.AutomorphicArithmetic.ShortNorms.normPrimesN
section
open GlobalTheory.Mem.An Filter Topology

namespace UpperTheory.T3

private lemma core_sqrt (A c c' t B Y : ℝ) (hA : 0 < A) (hc : 0 < c)
    (ht : 10000 ≤ t) (htA : 50 * A ≤ t) (htc : 13 / c ^ 2 ≤ t)
    (h2 : 40 * Real.exp (-(1 / 20) * t) ≤ c') (hB : 1 < B) (hBt : Real.log B ≤ 10 * t ^ 2)
    (hY : 0 < Y) (hYt : 8 * t ^ 5 ≤ Real.log Y) :
    1 ≤ Y ∧ Real.log B ≤ c * Real.sqrt (Real.log Y) ∧
      Y ^ ((9 : ℝ) / 10) ≤ c' * 1 * Y / (B ^ A * Real.log Y) := by
  have ht0 : 0 < t := by linarith
  have ht5 : 0 < t ^ 5 := pow_pos ht0 5
  have ht4 : 0 < t ^ 4 := pow_pos ht0 4
  have hL : 0 < Real.log Y := by linarith
  have hY1 : 1 < Y := by
    by_contra h
    push_neg at h
    have := Real.log_nonpos hY.le h
    linarith
  have ht1 : 1 ≤ t := by linarith
  have ht13 : t ≤ t ^ 3 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 3 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht35 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
  refine ⟨hY1.le, ?_, ?_⟩
  · have hS := Real.sq_sqrt hL.le
    have hS0 := Real.sqrt_nonneg (Real.log Y)
    have hc2 : 0 < c ^ 2 := pow_pos hc 2
    have hct : 13 ≤ c ^ 2 * t := by
      rw [div_le_iff₀ hc2] at htc
      linarith
    have hb : 10 * t ^ 2 ≤ c * Real.sqrt (Real.log Y) := by
      by_contra h
      push_neg at h
      have h1 := mul_self_lt_mul_self (mul_nonneg hc.le hS0) h
      have h2' : c * Real.sqrt (Real.log Y) * (c * Real.sqrt (Real.log Y)) = c ^ 2 * Real.log Y := by
        calc c * Real.sqrt (Real.log Y) * (c * Real.sqrt (Real.log Y))
            = c ^ 2 * (Real.sqrt (Real.log Y) ^ 2) := by ring
          _ = c ^ 2 * Real.log Y := by rw [hS]
      have h3 : c ^ 2 * (8 * t ^ 5) ≤ c ^ 2 * Real.log Y := mul_le_mul_of_nonneg_left hYt hc2.le
      have h4 : t ^ 4 * 13 ≤ t ^ 4 * (c ^ 2 * t) := mul_le_mul_of_nonneg_left hct ht4.le
      nlinarith
    linarith
  · have hB0 : 0 < B := by linarith
    have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) h2
    have hlogc' : -(1 / 20) * t ≤ Real.log c' := by
      have h := Real.log_le_log (by positivity) h2
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
      have : 0 < Real.log 40 := Real.log_pos (by norm_num)
      linarith
    have hlogL : Real.log (Real.log Y) ≤ 38 + Real.log Y / 40 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hL (show (0:ℝ) < 40 by norm_num))
      rw [Real.log_div hL.ne' (by norm_num)] at h1
      have h2' := Real.log_le_sub_one_of_pos (show (0:ℝ) < 40 by norm_num)
      linarith
    have hAB : A * Real.log B ≤ t ^ 3 / 5 := by
      have a1 : A * Real.log B ≤ A * (10 * t ^ 2) := mul_le_mul_of_nonneg_left hBt hA.le
      have a2 : A * (10 * t ^ 2) ≤ (t / 50) * (10 * t ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have a3 : (t / 50) * (10 * t ^ 2) = t ^ 3 / 5 := by ring
      linarith
    have hexpo : A * Real.log B + Real.log (Real.log Y) ≤ Real.log c' + Real.log Y / 10 := by
      linarith
    have lhs : B ^ A * Real.log Y = Real.exp (A * Real.log B + Real.log (Real.log Y)) := by
      rw [Real.exp_add, Real.exp_log hL, Real.rpow_def_of_pos hB0, mul_comm (Real.log B) A]
    have rhs : c' * Y ^ ((1:ℝ) / 10) = Real.exp (Real.log c' + Real.log Y / 10) := by
      rw [Real.exp_add, Real.exp_log hc'0, Real.rpow_def_of_pos hY]
      congr 2
      ring
    have hmain : B ^ A * Real.log Y ≤ c' * Y ^ ((1:ℝ) / 10) := by
      rw [lhs, rhs]
      exact Real.exp_le_exp.mpr hexpo
    have hden : 0 < B ^ A * Real.log Y := mul_pos (Real.rpow_pos_of_pos hB0 A) hL
    rw [le_div_iff₀ hden]
    calc Y ^ ((9:ℝ) / 10) * (B ^ A * Real.log Y) ≤ Y ^ ((9:ℝ) / 10) * (c' * Y ^ ((1:ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hY _).le
      _ = c' * 1 * (Y ^ ((9:ℝ) / 10) * Y ^ ((1:ℝ) / 10)) := by ring
      _ = c' * 1 * Y := by
          rw [← Real.rpow_add hY]
          norm_num

private lemma eventually_exp_decay_le (c' : ℝ) (hc' : 0 < c') :
    ∀ᶠ t : ℝ in atTop, 40 * Real.exp (-(1 / 20) * t) ≤ c' := by
  filter_upwards [eventually_ge_atTop (-20 * Real.log (c' / 40))] with t ht
  have h1 : -(1 / 20) * t ≤ Real.log (c' / 40) := by linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_log (div_pos hc' (by norm_num))] at h2
  linarith

private lemma ev_log_sq (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ (eps / 5) := by
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 10 by linarith)).bound one_pos
  filter_upwards [h1, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hxpos : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 < x ^ (eps / 10) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_pos hp, one_mul] at hx
  have e : x ^ (eps / 5) = x ^ (eps / 10) * x ^ (eps / 10) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  rw [e, sq]
  exact mul_le_mul hx hx hl hp.le

set_option maxHeartbeats 800000 in
theorem normPrimesN :
    ShortNorm → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d : ℕ, ModAt x eps N d → ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y →
      Y ^ ((9 : ℝ) / 10) ≤ ((normPrimes d N Y (2 * Y)).card : ℝ) := by
  intro hSN eps he
  unfold ShortNorm at hSN
  obtain ⟨A, c, c', hA, hc, hc', hmain⟩ := hSN
  have ht : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ 50 * A ≤ t ∧ 13 / c ^ 2 ≤ t ∧ 40 * Real.exp (-(1 / 20) * t) ≤ c' :=
    (eventually_ge_atTop 10000).and ((eventually_ge_atTop (50 * A)).and
      ((eventually_ge_atTop (13 / c ^ 2)).and (eventually_exp_decay_le c' hc')))
  have hx := (tendsto_rpow_atTop (show 0 < eps / 5 by linarith)).eventually ht
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hx.and ((ev_log_sq eps he).and (eventually_ge_atTop (1:ℝ))))
  refine ⟨x₀, fun x hxx N d hMod Y hY hlogY => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hls, hx1⟩ := hx₀ x hxx
  unfold ModAt at hMod
  obtain ⟨hdp, hd4, hd100, hN0, hdN, hlogN⟩ := hMod
  have hxpos : 0 < x := by linarith
  have ht5 : (x ^ (eps / 5)) ^ 5 = x ^ eps := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    push_cast
    ring
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hN0' : (0:ℝ) < N := by exact_mod_cast hN0
  have hdN' := Nat.le_of_dvd hN0 hdN
  have hdleN : (d:ℝ) ≤ N := by exact_mod_cast hdN'
  have hlogd : Real.log d ≤ Real.log N := Real.log_le_log hd0 hdleN
  have hN3 : 3 ≤ N := by omega
  have hd100' : (100:ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : 1 < 4 * (d:ℝ) * (N:ℝ) ^ 2 := by nlinarith
  have hlogB : Real.log (4 * (d:ℝ) * (N:ℝ) ^ 2) = Real.log 4 + Real.log d + 2 * Real.log N := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) hd0.ne') (pow_ne_zero _ hN0'.ne'),
      Real.log_mul (by norm_num) hd0.ne', Real.log_pow]
    push_cast
    ring
  have hBt : Real.log (4 * (d:ℝ) * (N:ℝ) ^ 2) ≤ 10 * (x ^ (eps / 5)) ^ 2 := by
    rw [hlogB]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    have q := mul_le_mul_of_nonneg_left hls (show 0 ≤ 3 * x ^ (eps / 5) by linarith)
    have big : 10000 * 10000 ≤ x ^ (eps / 5) * x ^ (eps / 5) := mul_le_mul t1 t1 (by norm_num) (by linarith)
    nlinarith
  have hYt : 8 * (x ^ (eps / 5)) ^ 5 ≤ Real.log Y := by rw [ht5]; exact hlogY
  obtain ⟨hY1, hsq, hfin⟩ := core_sqrt A c c' (x ^ (eps / 5)) (4 * (d:ℝ) * (N:ℝ) ^ 2) Y hA hc t1 t2 t3 t4 hB1 hBt hY hYt
  have hexp : Real.exp (-c * Real.sqrt (Real.log Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := Real.sqrt_nonneg (Real.log Y)
    nlinarith
  have key := hmain d N Y 1 hdp hd4 hd100 hN3 hY1 hsq hexp le_rfl
  have e : Y * (1 + 1) = 2 * Y := by ring
  rw [e] at key
  exact le_trans hfin key

end UpperTheory.T3
end

