module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.ChebyshevPrimeBoundsLogFact
section
noncomputable section

namespace PI.PC

open Real MeasureTheory Set

def phi (t : ℝ) : ℝ := Chebyshev.theta t / (t * log t ^ 2)

theorem phi_integrableOn {p : ℝ} (q : ℝ) (hp : 2 ≤ p) : IntegrableOn phi (Icc p q) volume := by
  have h : IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)) (Icc 2 q) volume :=
    Chebyshev.integrableOn_theta_div_id_mul_log_sq q
  exact h.mono_set (Icc_subset_Icc_left hp)

theorem phi_intervalIntegrable {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    IntervalIntegrable phi volume p q := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr (phi_integrableOn q hp)

theorem piece {p q c : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (hc : 0 < c) (hcp : c ≤ log p) :
    ∫ t in p..q, phi t ≤ log 4 / c ^ 2 * (q - p) := by
  have hconst : ∀ t ∈ Icc p q, phi t ≤ log 4 / c ^ 2 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlogt : c ≤ log t := le_trans hcp (Real.log_le_log (by linarith) ht.1)
    have hlpos : 0 < log t := lt_of_lt_of_le hc hlogt
    have hθ : Chebyshev.theta t ≤ log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    have hθ0 : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
    have hl4 : 0 ≤ log 4 := Real.log_nonneg (by norm_num)
    have hc2 : c ^ 2 ≤ log t ^ 2 := pow_le_pow_left₀ hc.le hlogt 2
    unfold phi
    rw [div_le_div_iff₀ (mul_pos ht0 (pow_pos hlpos 2)) (pow_pos hc 2)]
    calc Chebyshev.theta t * c ^ 2 ≤ (log 4 * t) * log t ^ 2 :=
          mul_le_mul hθ hc2 (sq_nonneg c) (mul_nonneg hl4 ht0.le)
      _ = log 4 * (t * log t ^ 2) := by ring
  have hint_r : IntervalIntegrable (fun _ : ℝ => log 4 / c ^ 2) volume p q := intervalIntegrable_const
  calc ∫ t in p..q, phi t ≤ ∫ t in p..q, log 4 / c ^ 2 :=
        intervalIntegral.integral_mono_on hpq (phi_intervalIntegrable hp hpq) hint_r hconst
    _ = log 4 / c ^ 2 * (q - p) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem dyadic (k : ℕ) : ∫ t in (2 : ℝ)..2 ^ (k + 1), phi t ≤
    2 / log 2 * ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hl2' : log 2 ≠ 0 := hl2.ne'
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have ha : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hb : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (phi_intervalIntegrable (le_refl 2) ha) (phi_intervalIntegrable ha hb)
    have hpiece : ∫ t in (2 : ℝ) ^ (k + 1)..2 ^ (k + 1 + 1), phi t ≤
        log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) :=
      piece ha hb (mul_pos (by positivity) hl2)
        (by rw [Real.log_pow]; norm_num)
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have heq : log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) =
        2 / log 2 * ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
      rw [h4]; first | (field_simp; ring) | field_simp
    rw [← hsplit, Finset.sum_range_succ, mul_add]
    linarith

theorem int_small : ∫ t in (2 : ℝ)..1024, phi t ≤ 61 := by
  have h := dyadic 9
  have h1024 : (2 : ℝ) ^ (9 + 1) = 1024 := by norm_num
  rw [h1024] at h
  have hs : ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 20.9 := by
    norm_num [Finset.sum_range_succ]
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hb : 2 / log 2 * ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 61 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  linarith

def gg (t : ℝ) : ℝ := 1.56 * (t / log t ^ 2) + 0.7 * log t

def gg' (t : ℝ) : ℝ := 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t

theorem gg_hasDerivAt {t : ℝ} (ht : 1 < t) : HasDerivAt gg (gg' t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (Real.log_pos ht).ne'
  have hL : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log ht0
  have hsq := hL.mul hL
  have hq := (hasDerivAt_id' t).div hsq (mul_ne_zero hl hl)
  have h := (hq.const_mul (1.56 : ℝ)).add (hL.const_mul (0.7 : ℝ))
  have hfun : gg = fun y => 1.56 * (y / (log y * log y)) + 0.7 * log y := by
    funext y; simp only [gg]; ring
  have hd : 1.56 * ((1 * (log t * log t) - t * (t⁻¹ * log t + log t * t⁻¹)) / (log t * log t) ^ 2)
      + 0.7 * t⁻¹ = gg' t := by
    show _ = 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t
    first | (field_simp; ring) | field_simp
  rw [hfun]
  exact h.congr_deriv hd

theorem chebyshevPrimeBounds_log_fact : log 1024 = 10 * log 2 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num

theorem int_tail (hU : CHUpper) {x : ℝ} (hx : 1024 ≤ x) :
    ∫ t in (1024 : ℝ)..x, phi t ≤ gg x - gg 1024 := by
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hpt : ∀ t ∈ Icc (1024 : ℝ) x, phi t ≤ gg' t := by
    intro t ht
    have ht1 : (1024 : ℝ) ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    have ht0' : t ≠ 0 := ht0.ne'
    have hL : 10 * log 2 ≤ log t := by
      rw [← chebyshevPrimeBounds_log_fact]; exact Real.log_le_log (by norm_num) ht1
    have hLpos : 0 < log t := by linarith
    have hL0 : log t ≠ 0 := hLpos.ne'
    have hψ := hU t (by linarith)
    have hθ := Chebyshev.theta_le_psi t
    unfold phi gg'
    rw [div_le_iff₀ (mul_pos ht0 (pow_pos hLpos 2))]
    have e : (1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t) * (t * log t ^ 2) =
        1.56 * t - 1.56 * 2 * t / log t + 0.7 * log t ^ 2 := by
      first | (field_simp; ring) | field_simp
    rw [e]
    have h3 : 1.56 * 2 * t / log t ≤ 0.4544 * t := by
      rw [div_le_iff₀ hLpos]
      nlinarith [mul_le_mul_of_nonneg_left hL ht0.le, mul_lt_mul_of_pos_left hl2 ht0]
    linarith
  have hderiv : ∀ t ∈ uIcc (1024 : ℝ) x, HasDerivAt gg (gg' t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact gg_hasDerivAt (by linarith [ht.1])
  have hcont : ContinuousOn gg' (uIcc 1024 x) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hl2' : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    have hl3 : log t ^ 3 ≠ 0 := pow_ne_zero 3 hl
    apply ContinuousAt.continuousWithinAt
    show ContinuousAt (fun s : ℝ => 1.56 * (1 / log s ^ 2 - 2 / log s ^ 3) + 0.7 / s) t
    fun_prop (disch := assumption)
  have hint_r : IntervalIntegrable gg' volume 1024 x := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_r
  have hmono : ∫ t in (1024 : ℝ)..x, phi t ≤ ∫ t in (1024 : ℝ)..x, gg' t :=
    intervalIntegral.integral_mono_on hx (phi_intervalIntegrable (by norm_num) hx) hint_r hpt
  exact hmono.trans_eq hftc

theorem gg_1024_nonneg : 0 ≤ gg 1024 := by
  have hl : 0 < log (1024 : ℝ) := Real.log_pos (by norm_num)
  have h1 : 0 ≤ (1024 : ℝ) / log 1024 ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  unfold gg
  linarith

theorem card_pr (y : ℝ) : (pr y).card = Nat.primeCounting ⌊y⌋₊ := by
  simp only [PI.pr, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  try (congr 1; ext p; simp)

theorem log_131072_eq_seventeen_mul_log_two : log 131072 = 17 * log 2 := by
  rw [show (131072 : ℝ) = 2 ^ 17 by norm_num, Real.log_pow]; norm_num

theorem log_sq_le {x : ℝ} (hx : 131072 ≤ x) : log x ^ 2 ≤ 0.00106 * x := by
  have hq : 1 ≤ x / 131072 := by rw [le_div_iff₀ (by norm_num)]; linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (x / 131072) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (x / 131072) := by
        first | exact Real.sqrt_le_sqrt hq | exact Real.sqrt_le_sqrt (by exact hq) | gcongr
  have hss : s ^ 2 = x / 131072 := by rw [hsdef]; exact Real.sq_sqrt (by linarith)
  have hxs : x = 131072 * s ^ 2 := by rw [hss]; ring
  have hlogs : log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogx : log x = log 131072 + 2 * log s := by
    rw [hxs, Real.log_mul (by norm_num) (pow_pos (by linarith) 2).ne', Real.log_pow]; norm_num
  have hl2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2' : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hup : log x ≤ 17 * log 2 - 2 + 2 * s := by rw [hlogx, log_131072_eq_seventeen_mul_log_two]; linarith
  have hlow : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ 17 * log 2 - 2 := by linarith
  have h1 : 17 * log 2 - 2 + 2 * s ≤ (17 * log 2) * s := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hs1)]
  have h2 : 0 ≤ 17 * log 2 - 2 + 2 * s := by linarith
  have hsq2 : log 2 ^ 2 ≤ 0.6931471808 ^ 2 := pow_le_pow_left₀ (by linarith) hl2.le 2
  have h3 : (17 * log 2) ^ 2 ≤ 138.86 := by nlinarith [hsq2]
  calc log x ^ 2 ≤ (17 * log 2 - 2 + 2 * s) ^ 2 := pow_le_pow_left₀ hlow hup 2
    _ ≤ ((17 * log 2) * s) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = (17 * log 2) ^ 2 * s ^ 2 := by ring
    _ ≤ 138.86 * s ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
    _ ≤ 0.00106 * (131072 * s ^ 2) := by nlinarith [sq_nonneg s]
    _ = 0.00106 * x := by rw [← hxs]

theorem pcLarge_of (hU : CHUpper) : PCLarge 131072 := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hL : 17 * log 2 ≤ log y := by
    rw [← log_131072_eq_seventeen_mul_log_two]; exact Real.log_le_log (by norm_num) hy
  have hL' : 11.78 ≤ log y := by linarith
  have hLpos : 0 < log y := by linarith
  have hLne : log y ≠ 0 := hLpos.ne'
  have hL2 := log_sq_le hy
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (phi_intervalIntegrable (le_refl 2) (by norm_num : (2 : ℝ) ≤ 1024))
    (phi_intervalIntegrable (by norm_num) (by linarith : (1024 : ℝ) ≤ y))
  have hI : ∫ t in (2 : ℝ)..y, phi t ≤ 61 + gg y := by
    have h1 := int_small
    have h2 := int_tail hU (by linarith : (1024 : ℝ) ≤ y)
    have h3 := gg_1024_nonneg
    rw [← hsplit]
    linarith
  unfold gg at hI
  have hθ : Chebyshev.theta y ≤ 1.1056 * y + 0.7 * log y ^ 2 :=
    (Chebyshev.theta_le_psi y).trans (hU y (by linarith))
  have hdl : y / log y ^ 2 * log y = y / log y := by
    first | rw [pow_two, div_mul_eq_mul_div, mul_div_mul_right _ _ hLne] | (field_simp; ring) | field_simp
  have e : (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y =
      61 * log y + 1.56 * (y / log y) + 0.7 * log y ^ 2 := by
    rw [← hdl]; ring
  have hv : y / log y ≤ 0.085 * y := by
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_le_mul_of_nonneg_left hL' hy0.le]
  have hLle : log y ≤ 0.00009 * y := by
    nlinarith [mul_le_mul_of_nonneg_left hL' hLpos.le]
  have key : Chebyshev.theta y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y < 1.26 * y := by
    nlinarith [e, hθ, hv, hLle, hL2, hy0]
  have hfin : Chebyshev.theta y / log y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) < 1.26 * y / log y := by
    rw [div_add' _ _ _ hLne]
    first | exact div_lt_div_of_pos_right key hLpos | exact (div_lt_div_iff_of_pos_right hLpos).mpr key | gcongr
  rw [card_pr, Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
  show Chebyshev.theta y / log y + ∫ t in (2 : ℝ)..y, phi t < 1.26 * y / log y
  linarith

end PI.PC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.CountSuccLe
section
namespace PI.PC

open Real

theorem tst_sound {m c c' : ℕ} (h : tst m c = true) (hc : c' ≤ c) (hm : 1 ≤ m) :
    (c' : ℝ) * log m < 1.26 * m := by
  unfold tst at h
  rw [Nat.blt_eq] at h
  obtain ⟨q, hqdef⟩ : ∃ q, q = (3225600000000 * m - 1) / (c * 6931471808) := ⟨_, rfl⟩
  rw [← hqdef] at h
  have hm256 : 1 ≤ m ^ 256 := Nat.one_le_pow 256 m hm
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      subst h0
      have hq0 : q = 0 := by rw [hqdef]; simp
      rw [hq0, pow_zero] at h
      exact absurd h (not_lt.mpr hm256)
    · exact h0
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ log (m : ℝ) := Real.log_nonneg hmR
  have h1 : 256 * log (m : ℝ) < q * log 2 := by
    have hR : ((m : ℝ)) ^ 256 < (2 : ℝ) ^ q := by exact_mod_cast h
    have hl := Real.log_lt_log (by positivity) hR
    rw [Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith
  have h2 : (q : ℝ) * c * 6931471808 < 3225600000000 * m := by
    have hN : q * (c * 6931471808) ≤ 3225600000000 * m - 1 := by
      rw [hqdef]; exact Nat.div_mul_le_self _ _
    have hpos : 0 < 3225600000000 * m := by positivity
    have hN' : q * (c * 6931471808) < 3225600000000 * m :=
      Nat.lt_of_le_of_lt hN (Nat.sub_lt hpos one_pos)
    have hC : ((q * (c * 6931471808) : ℕ) : ℝ) < ((3225600000000 * m : ℕ) : ℝ) := by
      exact_mod_cast hN'
    push_cast at hC
    linarith
  have h3 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hqc : (0 : ℝ) ≤ q * c := by positivity
  have h4 : (c : ℝ) * (256 * log m) < c * (q * log 2) := mul_lt_mul_of_pos_left h1 hcR
  have h5 : ((q : ℝ) * c) * log 2 ≤ (q * c) * 0.6931471808 := mul_le_mul_of_nonneg_left h3.le hqc
  have h6 : (c' : ℝ) * log m ≤ c * log m :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlogm
  nlinarith [h4, h5, h6, h2]

theorem loop_sound (B : ℕ) : ∀ k n c Q : ℕ, loop B k n c Q = true → 1 ≤ n →
    Nat.count Nat.Prime n ≤ c → (∀ p, p.Prime → n ≤ p → Nat.Coprime p Q) →
    ∀ m, n ≤ m → m < n + k → ∃ c', Nat.count Nat.Prime (m + 1) ≤ c' ∧ tst m c' = true := by
  intro k
  induction k with
  | zero =>
    intro n c Q _ _ _ _ m hnm hmk
    omega
  | succ k ih =>
    intro n c Q hrun hn hcount hcop m hnm hmk
    simp only [loop, force_eq] at hrun
    by_cases hg : Nat.gcd n Q = 1
    · rw [if_pos hg, Bool.and_eq_true] at hrun
      obtain ⟨hb, hrest⟩ := hrun
      have hc1 : Nat.count Nat.Prime (n + 1) ≤ c + 1 := by
        rw [Nat.count_succ]; split_ifs <;> omega
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · exact ⟨c + 1, hc1, hb⟩
      · refine ih (n + 1) (c + 1) _ hrest (by omega) hc1 ?_ m hlt (by omega)
        intro p hp hnp
        split_ifs
        · exact Nat.Coprime.mul_right (hcop p hp (by omega))
            ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
        · exact hcop p hp (by omega)
    · rw [if_neg hg, Bool.and_eq_true] at hrun
      obtain ⟨hb, hrest⟩ := hrun
      have hnp : ¬ n.Prime := fun hp => hg (hcop n hp le_rfl)
      have hc0 : Nat.count Nat.Prime (n + 1) ≤ c := by
        rw [Nat.count_succ, if_neg hnp]; omega
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · exact ⟨c, hc0, hb⟩
      · exact ih (n + 1) c Q hrest (by omega) hc0 (fun p hp hnp' => hcop p hp (by omega)) m hlt
          (by omega)

theorem count_succ_le (n : ℕ) : Nat.count Nat.Prime (n + 1) ≤ n := by
  induction n with
  | zero => simp [Nat.count_succ, Nat.not_prime_zero]
  | succ n ih =>
    rw [Nat.count_succ]
    split_ifs <;> omega

theorem small_nat (m : ℕ) (h1 : 1 ≤ m) (h2 : m < 131072) :
    (Nat.count Nat.Prime (m + 1) : ℝ) * log m < 1.26 * m := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
  · norm_num
  · have hc2 : Nat.count Nat.Prime 2 ≤ 0 := by
      show Nat.count Nat.Prime (0 + 1 + 1) ≤ 0
      simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]
    obtain ⟨c', hc', hb⟩ := loop_sound 362 131070 2 0 1 loop_run (by norm_num) hc2
      (fun p _ _ => Nat.coprime_one_right p) m h1' (by omega)
    exact tst_sound hb hc' h1

theorem real_of_nat {n k : ℕ} {y : ℝ} (hn : 1 ≤ n) (hk : k ≤ n) (h : (k : ℝ) * log n < 1.26 * n)
    (hy : (n : ℝ) ≤ y) : (k : ℝ) * log y < 1.26 * y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hy0 : 0 < y := lt_of_lt_of_le hn' hy
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : log y - log n ≤ y / n - 1 := by
    rw [← Real.log_div hy0.ne' hn'.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hy0 hn')
  have ht : 0 ≤ y / n - 1 := sub_nonneg.mpr ((one_le_div hn').mpr hy)
  have hnt : (n : ℝ) * (y / n - 1) = y - n := by
    rw [mul_sub, mul_div_cancel₀ y hn'.ne', mul_one]
  have h1 : (k : ℝ) * (log y - log n) ≤ k * (y / n - 1) := mul_le_mul_of_nonneg_left hlog hk0
  have h2 : (k : ℝ) * (y / n - 1) ≤ n * (y / n - 1) := mul_le_mul_of_nonneg_right hkR ht
  nlinarith [h, h1, h2, hnt, hy]

theorem pr_card (y : ℝ) : (pr y).card = Nat.count Nat.Prime (⌊y⌋₊ + 1) := by
  rw [Nat.count_eq_card_filter_range]
  rfl

theorem pcSmall : PCSmall 131072 := by
  unfold PCSmall
  intro y hy1 hy2
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1.le)
  have hm2 : ⌊y⌋₊ < 131072 := (Nat.floor_lt hy0).mpr (by exact_mod_cast hy2)
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hA := small_nat _ hm1 hm2
  have hB := real_of_nat hm1 (count_succ_le _) hA hfl
  have hlog : 0 < log y := Real.log_pos hy1
  rw [pr_card, lt_div_iff₀ hlog]
  exact hB

end PI.PC
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiUpperBoundOfLtThirtyMulSixPow
section
namespace PI.PC

open Real

theorem log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log_six : log 6 = log 2 + log 3 := by
  rw [← log_mul (by norm_num) (by norm_num)]
  norm_num

theorem chebyshevConstantNumeric : ANum := by
  have h2 := log_two_gt_d9
  have h2' := log_two_lt_d9
  have h3 := log_three_gt_d9
  have h3' := log_three_lt_d9
  have h5 := log_five_gt_d9
  have h5' := log_five_lt_d9
  unfold ANum chA
  rw [log_thirty]
  constructor <;> norm_num at * <;> linarith

theorem lcmUpto_le_three_pow : ∀ n < 30, Nat.lcmUpto n ≤ 3 ^ n := by
  decide +kernel

theorem psi_le_of_lt_thirty {x : ℝ} (h0 : 0 ≤ x) (hx : x < 30) : Chebyshev.psi x ≤ 1.1056 * x := by
  have hn : ⌊x⌋₊ < 30 := (Nat.floor_lt h0).2 (by exact_mod_cast hx)
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have h1 : ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ ⌊x⌋₊ := by
    exact_mod_cast lcmUpto_le_three_pow _ hn
  have h2 : log ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ log ((3 : ℝ) ^ ⌊x⌋₊) :=
    log_le_log (by exact_mod_cast Nat.lcmUpto_pos _) h1
  rw [log_pow] at h2
  have h3 := log_three_lt_d9
  have h4 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le h0
  have h5 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : ((⌊x⌋₊ : ℕ) : ℝ) * log 3 ≤ ((⌊x⌋₊ : ℕ) : ℝ) * 1.1056 :=
    mul_le_mul_of_nonneg_left (by norm_num at h3 ⊢; linarith) h5
  nlinarith

theorem psiUpperBound_of_lt_thirty_mul_six_pow (hA : ANum) (hD : DUpper) (hS : Sandwich) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x < 30 * 6 ^ k → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2 := by
  induction k with
  | zero =>
    intro x h1 hx
    have := psi_le_of_lt_thirty (by linarith) (by simpa using hx)
    have := sq_nonneg (log x)
    linarith
  | succ k ih =>
    intro x h1 hx
    rcases lt_or_ge x 30 with h30 | h30
    · have := psi_le_of_lt_thirty (by linarith) h30
      have := sq_nonneg (log x)
      linarith
    · have hx6 : x / 6 < 30 * 6 ^ k := by
        rw [div_lt_iff₀ (by norm_num)]
        calc x < 30 * 6 ^ (k + 1) := hx
          _ = 30 * 6 ^ k * 6 := by ring
      have e1 := ih (x / 6) (by linarith) hx6
      have e2 := (hS x (by linarith)).1
      have e3 := hD x h30
      have e4 : chA * x ≤ 0.9213 * x := mul_le_mul_of_nonneg_right hA.2 (by linarith)
      have hl : log (x / 6) = log x - log 6 := log_div (by linarith) (by norm_num)
      rw [hl] at e1
      have hL : 0 ≤ log x := log_nonneg h1
      have l6a : 1.7917 ≤ log 6 := by
        rw [log_six]; have := log_two_gt_d9; have := log_three_gt_d9; norm_num at *; linarith
      have l6b : log 6 ≤ 1.7918 := by
        rw [log_six]; have := log_two_lt_d9; have := log_three_lt_d9; norm_num at *; linarith
      have p1 : 0 ≤ (1.4 * log 6 - 2.5) * log x := mul_nonneg (by linarith) hL
      have p2 : (log 6) ^ 2 ≤ 1.7918 ^ 2 := pow_le_pow_left₀ (by linarith) l6b 2
      nlinarith

theorem chUpper_of (hA : ANum) (hD : DUpper) (hS : Sandwich) : CHUpper := by
  intro x h1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 6)
  refine psiUpperBound_of_lt_thirty_mul_six_pow hA hD hS k x h1 ?_
  have : (0 : ℝ) < 6 ^ k := by positivity
  linarith

end PI.PC
end

