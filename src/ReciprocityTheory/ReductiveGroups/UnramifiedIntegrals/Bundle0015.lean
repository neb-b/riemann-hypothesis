module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

private theorem norm_finsum_le_of_forall_norm_le_univ_sort {α : Type*} (f : α → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖∑ᶠ a, f a‖ ≤ C := by
  classical
  rw [finsum_def]
  split_ifs with hs
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  · simpa using hC

private theorem mvPowerSeries_norm_coeff_mul_le_mul {ι : Type} {F G : MvPowerSeries ι K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ a) (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ b) :
    ∀ e, ‖MvPowerSeries.coeff e (F * G)‖ ≤ a * b := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha

private theorem mvPowerSeries_norm_coeff_pow_le_pow {ι : Type} {F : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ c) :
    ∀ (m : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ c ^ m := by
  classical
  intro m
  induction m with
  | zero =>
    intro e
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc m) hc ih hF

private theorem mvPowerSeries_norm_coeff_pow_le_one {ι : Type} {F : MvPowerSeries ι K}
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ 1) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ 1 := by
  simpa using mvPowerSeries_norm_coeff_pow_le_pow zero_le_one hF m e

private theorem mvPowerSeries_norm_coeff_pow_sub_pow_le {ι : Type} {A B : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ e, ‖MvPowerSeries.coeff e A‖ ≤ 1) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ m - B ^ m)‖ ≤ c := by
  classical
  have hs : ∀ e, ‖MvPowerSeries.coeff e (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i))‖ ≤ 1 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one zero_le_one (mvPowerSeries_norm_coeff_pow_le_one hA i) (mvPowerSeries_norm_coeff_pow_le_one hB (m - 1 - i)) e
  rw [← geom_sum₂_mul]
  simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one hc hs hAB e

private theorem mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {A B : MvPowerSeries ι K}
    {c : ℝ} (hc : 0 ≤ c) (hcl : c ≤ ‖(l : K)‖) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ l - B ^ l)‖ ≤ c * ‖(l : K)‖ := by
  classical
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by ring⟩
  simp only [add_sub_cancel_right] at hAB
  have hc1 : c ≤ 1 := hcl.trans hl1.le
  have hl2 : 2 ≤ l := hl.two_le
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc (norm_nonneg _))
    fun i hi => ?_
  have hi' : i < l := Finset.mem_range.mp hi
  rw [← Nat.cast_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  have hterm : ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖ ≤ c ^ (i + 1) := by
    simpa using mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc _) zero_le_one (mvPowerSeries_norm_coeff_pow_le_pow hc hAB (i + 1)) (mvPowerSeries_norm_coeff_pow_le_one hB _) e
  have hch : ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) ≤ c * ‖(l : K)‖ := by
    obtain h | h : i + 1 < l ∨ i + 1 = l := by omega
    · obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero i) h
      rw [hq, Nat.cast_mul, norm_mul]
      have hq1 : ‖(q : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K q
      have hpc : c ^ (i + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero i)
      calc ‖(l : K)‖ * ‖(q : K)‖ * c ^ (i + 1) ≤ ‖(l : K)‖ * 1 * c := by
            gcongr
        _ = c * ‖(l : K)‖ := by ring
    · rw [h, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
      obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
      have hpc : c ^ (j + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero j)
      calc c ^ (j + 2) = c * c ^ (j + 1) := by ring
        _ ≤ c * ‖((j + 2 : ℕ) : K)‖ := by gcongr; exact hpc.trans hcl
  calc ‖((l.choose (i + 1) : ℕ) : K)‖ * ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖
      ≤ ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) := by gcongr
    _ ≤ c * ‖(l : K)‖ := hch

private theorem mvPowerSeries_norm_coeff_pow_prime_pow_sub_le {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P Q : MvPowerSeries ι K}
    (hQ : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1)
    (hPQ : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) :
    ∀ (v : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (P ^ (l ^ v) - Q ^ (l ^ v))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
  intro v
  induction v with
  | zero => simpa using hPQ
  | succ v ih =>
    intro e
    rw [pow_succ, pow_mul, pow_mul, pow_succ _ (v + 1)]
    exact mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm hl hl1 (pow_nonneg (norm_nonneg _) _)
      (pow_le_of_le_one (norm_nonneg _) hl1.le (Nat.succ_ne_zero v)) (mvPowerSeries_norm_coeff_pow_le_one hQ _) ih e

private theorem norm_natCast_eq_one_of_not_prime_dvd (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime l m := (Nat.coprime_or_dvd_of_prime hl m).resolve_right hm
  have h1 := Nat.gcd_eq_gcd_ab l m
  rw [hcop.gcd_eq_one] at h1
  have h2 : (1 : K) = (l : K) * (Nat.gcdA l m : K) + (m : K) * (Nat.gcdB l m : K) := by
    have h3 := congrArg (fun x : ℤ => (x : K)) h1
    push_cast at h3
    exact h3
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) (not_lt.mp fun hlt => ?_)
  have h4 : ‖(1 : K)‖ < 1 := by
    rw [h2]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(l : K)‖ * ‖((Nat.gcdA l m : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hl1
    · rw [norm_mul]
      calc ‖(m : K)‖ * ‖((Nat.gcdB l m : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hlt
  simp at h4

theorem qls {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative z)) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) (P - Q)) :
    DivByMv (l : K) (z.subst P - z.subst Q) := by
  classical
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have hQs : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hPi : ∀ e, ‖MvPowerSeries.coeff e P‖ ≤ 1 := by
    unfold IntegralMv at hP
    exact hP
  have hQi : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1 := by
    unfold IntegralMv at hQ
    exact hQ
  have hPQi : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖ := by
    unfold DivByMv at hPQ
    exact hPQ
  have hzi : ∀ n, ‖PowerSeries.coeff n (derivative z)‖ ≤ 1 := by
    unfold IntegralPS at hz
    exact hz
  have hpow := mvPowerSeries_norm_coeff_pow_prime_pow_sub_le hl hl1 hQi hPQi
  have hterm : ∀ (d : ℕ) (e : ι →₀ ℕ),
      ‖PowerSeries.coeff d z • MvPowerSeries.coeff e (P ^ d) -
        PowerSeries.coeff d z • MvPowerSeries.coeff e (Q ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d e
    rw [← smul_sub, ← map_sub, norm_smul]
    rcases d with _ | k
    · have h0 : PowerSeries.coeff 0 z = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hz0
      rw [h0, norm_zero, zero_mul]
      exact norm_nonneg _
    · obtain ⟨v, m, hm, hkm0⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
      have hkm : k + 1 = l ^ v * m := hkm0
      have hz' : ‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖ ≤ 1 := by
        have h1 := hzi k
        rw [PowerSeries.coeff_derivative] at h1
        simpa [norm_mul] using h1
      have hn : ‖((k + 1 : ℕ) : K)‖ = ‖(l : K)‖ ^ v := by
        rw [hkm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, norm_natCast_eq_one_of_not_prime_dvd hl hl1 hm, mul_one]
      have hPQn : ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
        rw [hkm, pow_mul, pow_mul]
        exact mvPowerSeries_norm_coeff_pow_sub_pow_le (pow_nonneg (norm_nonneg _) _) (mvPowerSeries_norm_coeff_pow_le_one hPi _) (mvPowerSeries_norm_coeff_pow_le_one hQi _) (hpow v) m e
      calc ‖PowerSeries.coeff (k + 1) z‖ * ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖
          ≤ ‖PowerSeries.coeff (k + 1) z‖ * ‖(l : K)‖ ^ (v + 1) := by gcongr
        _ = (‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖) * ‖(l : K)‖ := by
          rw [hn, pow_succ, mul_assoc]
        _ ≤ 1 * ‖(l : K)‖ := by gcongr
        _ = ‖(l : K)‖ := one_mul _
  unfold DivByMv
  intro e
  rw [map_sub, PowerSeries.coeff_subst hPs, PowerSeries.coeff_subst hQs,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hPs z e)
      (PowerSeries.coeff_subst_finite hQs z e)]
  exact norm_finsum_le_of_forall_norm_le_univ_sort _ (norm_nonneg _) fun d => hterm d e

theorem qls1 (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative z)) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) (P - Q)) :
    DivBy (l : K) (z.subst P - z.subst Q) := by
  have key : ∀ (F : PowerSeries K) (d : Unit →₀ ℕ),
      MvPowerSeries.coeff d F = PowerSeries.coeff (d ()) F := by
    intro F d
    conv_lhs => rw [Finsupp.unique_single d]
    rfl
  have hP' : IntegralMv P := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hP _
  have hQ' : IntegralMv Q := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hQ _
  have hPQ' : DivByMv (l : K) (P - Q) := by
    unfold DivByMv
    intro d
    rw [key]
    exact hPQ _
  have h := qls hl hl1 z hz0 hz P Q hP0 hQ0 hP' hQ' hPQ'
  unfold DivBy
  intro k
  have hk := h (Finsupp.single () k)
  rwa [key, Finsupp.single_eq_same] at hk

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)

theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ (jT τ) := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m) :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (DD_ne_zero τ))
    · exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)
  · rintro ⟨r, hr⟩
    have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  · rw [← h1, h2]; ring

end ReciprocityTheory.ChartRestriction.L1
end
end

