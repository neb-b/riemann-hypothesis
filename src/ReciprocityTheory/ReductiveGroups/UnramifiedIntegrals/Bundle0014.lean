module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgFinA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩


omit [IsUltrametricDist K] [CharZero K] in
theorem ltLog_sub_eq_X (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ (f : PowerSeries K) {k : ℕ} (_ : k ≠ 0) (m : ℕ),
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
    rw [PowerSeries.coeff_subst' ha]
    simp only [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [finsum_eq_single _ q]
      · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
      · intro d hd
        have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
        simp [this]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro d
      have : m ≠ k * d := fun h => hd ⟨d, h⟩
      simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dite_eq_left hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq (Nat.find_spec hex)).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rcases j with _ | j
    · have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
      have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
        rw [h1]
        intro h
        have := Nat.le_of_dvd one_pos h
        omega
      rw [if_neg hnd, hpow 0, h1, if_pos rfl]
      simp
    · have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
        rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ (by omega)]
      have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
        have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
        omega
      rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
        if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
      ring
  · have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dite_eq_right hn]
    have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
    rw [h0, if_neg hX]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
      rw [Nat.mul_div_cancel_left m (by omega), PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
        dite_eq_right hm, map_zero]
      simp
    · simp

theorem ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X


omit [IsUltrametricDist K] [CharZero K] in
theorem isFunEqType_of_mv {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp only [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h (Finsupp.single () n)
  | exact (by unfold IntegralMv at h; exact h (Finsupp.single () n))

omit [IsUltrametricDist K] [CharZero K] in
theorem inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring

theorem fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by
  have hl2 : 2 ≤ l := hF.prime.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 (by rw [hcε, h, mul_zero])
  have hXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) := PowerSeries.HasSubst.X_pow hq

  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf00 : constantCoeff f0 = 0 := by
    rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ (σ ε))⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul hXq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C (by rw [norm_inv, hε, inv_one])) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T : IsFunEqType l (l ^ 2) (σ.comp σ) f1 :=
    isFunEqType_of_mv hq _ _ (Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 hf00 hf0T Unit α
      hα0 ((integralPS_iff_mv α).1 hαI))
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf10 : constantCoeff f1 = 0 := by
    rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hlam0]; simp
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) hf10 hf11
    hf1T (ltLog_const l hl2) (ltLog_type hl2 _)
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst (C ε * h) := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have hlams : PowerSeries.HasSubst lam := PowerSeries.HasSubst.of_constantCoeff_zero' hlam0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]; rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply hlams hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgGauss
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def LeadAt (f : PowerSeries K) (r : ℝ) (i : ℕ) : Prop :=
  0 < r ∧ (∀ n, ‖coeff n f‖ ≤ r) ∧ (∀ n, n < i → ‖coeff n f‖ < r) ∧ ‖coeff i f‖ = r

theorem gauss_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem gauss_norm_sum_lt {α : Type} (s : Finset α) (f : α → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ s, ‖f a‖ < r) : ‖∑ a ∈ s, f a‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hr
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

theorem LeadAt.mul {f g : PowerSeries K} {r s : ℝ} {i j : ℕ} (hf : LeadAt f r i) (hg : LeadAt g s j) :
    LeadAt (f * g) (r * s) (i + j) := by
  obtain ⟨hr, hf1, hf2, hf3⟩ := hf
  obtain ⟨hs, hg1, hg2, hg3⟩ := hg
  have small : ∀ p q : ℕ, (p < i ∨ q < j) → ‖coeff p f * coeff q g‖ < r * s := by
    intro p q hpq
    rw [norm_mul]
    rcases hpq with hp | hq
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ ‖coeff p f‖ * s :=
            mul_le_mul_of_nonneg_left (hg1 q) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_right (hf2 p hp) hs
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ r * ‖coeff q g‖ :=
            mul_le_mul_of_nonneg_right (hf1 p) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_left (hg2 q hq) hr
  refine ⟨mul_pos hr hs, fun n => ?_, fun n hn => ?_, ?_⟩
  · rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos hr hs).le fun x _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hf1 _) (hg1 _) (norm_nonneg _) hr.le
  · rw [coeff_mul]
    refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    omega
  · have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hlt : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j), coeff x.1 f * coeff x.2 g‖ < r * s := by
      refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra hc
      push Not at hc
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    have hij : ‖coeff i f * coeff j g‖ = r * s := by rw [norm_mul, hf3, hg3]
    rw [gauss_norm_add_of_lt (by rwa [hij]), hij]

theorem leadAt_one : LeadAt (1 : PowerSeries K) 1 0 := by
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem leadAt_C {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by
  refine ⟨norm_pos_iff.mpr hc, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_C]
  split_ifs <;> simp

theorem leadAt_factor {A : PowerSeries K} (hA : IntegralPS A) (hA0 : constantCoeff A = 1) (x : K) :
    ∃ i, i ≤ 2 ∧ LeadAt (A - C x * X ^ 2) (max 1 ‖x‖) i := by
  have hc : ∀ n, coeff n (A - C x * X ^ 2) = coeff n A - if n = 2 then x else 0 := by
    intro n
    rw [map_sub, coeff_C_mul_X_pow]
  by_cases hx : ‖x‖ ≤ 1
  · refine ⟨0, by norm_num, ?_⟩
    rw [max_eq_left hx]
    refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), ?_⟩
    · rw [hc]
      split_ifs
      · rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA n) (by rw [norm_neg]; exact hx))
      · rw [sub_zero]; exact hA n
    · rw [hc, if_neg (by norm_num), sub_zero, coeff_zero_eq_constantCoeff_apply, hA0, norm_one]
  · push Not at hx
    refine ⟨2, le_rfl, ?_⟩
    rw [max_eq_right hx.le]
    have h2 : ‖coeff 2 A - x‖ = ‖x‖ := by
      rw [sub_eq_neg_add, gauss_norm_add_of_lt (by rw [norm_neg]; exact (hA 2).trans_lt hx), norm_neg]
    refine ⟨one_pos.trans hx, fun n => ?_, fun n hn => ?_, ?_⟩
    · rw [hc]
      split_ifs with h
      · subst h; exact h2.le
      · rw [sub_zero]; exact (hA n).trans hx.le
    · rw [hc, if_neg (by omega), sub_zero]
      exact (hA n).trans_lt hx
    · rw [hc, if_pos rfl, h2]

theorem leadAt_prod {α : Type} (S : Finset α) (x : α → K) {A : PowerSeries K} (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) :
    ∃ i, i ≤ 2 * S.card ∧ LeadAt (∏ P ∈ S, (A - C (x P) * X ^ 2)) (∏ P ∈ S, max 1 ‖x P‖) i := by
  classical
  refine Finset.induction_on S ⟨0, le_rfl, by simpa using leadAt_one⟩ ?_
  intro a T ha ih
  obtain ⟨i, hi, h⟩ := ih
  obtain ⟨j, hj, h'⟩ := leadAt_factor hA hA0 (x a)
  refine ⟨j + i, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]; omega
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h'.mul h

theorem gauss_bound {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨i, -, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc).mul h
  rw [← hl.2.2.2]
  exact hG _

theorem gauss_unit {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K) (hc : ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ = 1) :
    ∃ i, i ≤ 2 * S.card ∧ ‖coeff i (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))‖ = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨i, hi, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc0).mul h
  exact ⟨0 + i, by omega, hl.2.2.2.trans hc⟩

theorem leadAt_first_unit {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by
  classical
  refine ⟨Nat.find h, fun i hi => Nat.find_min' h hi, one_pos, hg,
    fun n hn => lt_of_le_of_ne (hg n) (Nat.find_min h hn), Nat.find_spec h⟩

theorem unit_coeff_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g)
    (hf0 : ‖constantCoeff f‖ = 1) (N : ℕ) (h : ∃ i, i ≤ N ∧ ‖coeff i g‖ = 1) :
    ∃ i, i ≤ N ∧ ‖coeff i (f * g)‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨i₀, hmin, hl⟩ := leadAt_first_unit hg ⟨i, hi⟩
  have hf' : LeadAt f 1 0 := ⟨one_pos, hf, fun n hn => absurd hn (Nat.not_lt_zero _),
    by rw [coeff_zero_eq_constantCoeff_apply, hf0]⟩
  have hm := hf'.mul hl
  refine ⟨0 + i₀, by have := hmin i hi; omega, ?_⟩
  rw [hm.2.2.2, one_mul]

theorem unit_coeff_of_sq {e : PowerSeries K} (he : IntegralPS e) (N : ℕ)
    (h : ∃ i, i ≤ 2 * N ∧ ‖coeff i (e ^ 2)‖ = 1) : ∃ i, i ≤ N ∧ ‖coeff i e‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  have hex : ∃ j, ‖coeff j e‖ = 1 := by
    by_contra hno
    push Not at hno
    have hlt : ∀ n, ‖coeff n e‖ < 1 := fun n => lt_of_le_of_ne (he n) (hno n)
    have : ‖coeff i (e ^ 2)‖ < 1 := by
      rw [sq, coeff_mul]
      refine gauss_norm_sum_lt _ _ one_pos fun x _ => ?_
      rw [norm_mul]
      calc ‖coeff x.1 e‖ * ‖coeff x.2 e‖ ≤ ‖coeff x.1 e‖ * 1 :=
            mul_le_mul_of_nonneg_left (he _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hlt _
    exact this.ne hi
  obtain ⟨j, -, hl⟩ := leadAt_first_unit he hex
  have hm := hl.mul hl
  rw [one_mul, ← sq] at hm
  refine ⟨j, ?_, hl.2.2.2⟩
  by_contra hc
  push Not at hc
  exact (hm.2.2.1 i (by omega)).ne hi

theorem integral_of_sq_eq {e U G : PowerSeries K} (he : IntegralPS e) (he0 : constantCoeff e = 0)
    (hU : IntegralPS U) (hU0 : constantCoeff U = 1) (h : e ^ 2 = X ^ 2 * U * G) : IntegralPS G := by
  obtain ⟨e', rfl⟩ := (PowerSeries.X_dvd_iff).mpr he0
  have he' : IntegralPS e' := fun n => by
    have := he (n + 1)
    rwa [coeff_succ_X_mul] at this
  have h2 : e' ^ 2 = U * G := by
    have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← h]
    ring
  have hUi : IntegralPS U⁻¹ := integralPS_inv hU (by rw [hU0, norm_one])
  have hG : G = U⁻¹ * e' ^ 2 := by
    rw [h2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hU0]; exact one_ne_zero), one_mul]
  rw [hG]
  exact integralPS_mul hUi (integralPS_pow he' 2)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem powerSeries_subst_subst_of_constantCoeff_zero {R : Type} [CommRing R] {α β : Type} (φ : PowerSeries R)
    {u : MvPowerSeries α R} (hu : MvPowerSeries.constantCoeff u = 0) {b : α → MvPowerSeries β R}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem mulN_integral {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} (h : LawD lam Φ) (n : ℕ) :
    ∃ e : PowerSeries K, constantCoeff e = 0 ∧ IntegralPS e ∧ lam.subst e = C (n : K) * lam := by
  have hXs : lam.subst (X : PowerSeries K) = lam := by
    have ha1 : PowerSeries.HasSubst (X : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
    ext m
    rw [PowerSeries.coeff_subst' ha1]
    rw [finsum_eq_single _ m]
    · rw [PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
    · intro d hd
      rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]
  induction n with
  | zero =>
    refine ⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩
    ext k
    rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (map_zero _)),
      Nat.cast_zero, map_zero, zero_mul, map_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]
    · rw [zero_pow hd.ne', map_zero, smul_zero]
  | succ n ih =>
    obtain ⟨e, he0, he, hlog⟩ := ih
    have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0 := by
      intro s
      fin_cases s
      · exact he0
      · exact PowerSeries.constantCoeff_X
    have hPint : ∀ s, IntegralMv ((![e, X] : Fin 2 → PowerSeries K) s) := by
      intro s
      fin_cases s
      · exact (integralPS_iff_mv e).mp he
      · exact (integralPS_iff_mv _).mp integralPS_X
    have ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K) :=
      ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    refine ⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩
    · have h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd : d = 0
        · rw [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]
        · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact hd (Finsupp.ext hc)
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
            Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, hP0 s, zero_pow hs]),
            smul_zero]
      exact h0
    · exact (integralPS_iff_mv _).mpr (integralMv_subst2 h.Φint hP0 hPint)
    · rw [← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]
      unfold atX atY
      first
      | rw [MvPowerSeries.subst_add ha]
      | rw [← MvPowerSeries.coe_substAlgHom ha, map_add (f := _), MvPowerSeries.coe_substAlgHom]
      rw [powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha,
        powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha,
        MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hlog, hXs, Nat.cast_succ, map_add (f := _), map_one]
      ring

end ReciprocityTheory.ChartRestriction.L1
end
end

