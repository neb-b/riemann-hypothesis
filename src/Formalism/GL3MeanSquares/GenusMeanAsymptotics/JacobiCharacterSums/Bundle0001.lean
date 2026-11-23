module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExistsFarFromPoints
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem pow_key (x : ℝ) (hx0 : 0 < x) (a k : ℕ) (hka : k ≤ a) :
    x ^ (a + k) ≤ (5 * x) ^ a * (x / 5) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hka
  have hx : (5 * x) ^ (k + m) * (x / 5) ^ k = 5 ^ m * x ^ (k + m + k) := by
    rw [mul_pow, div_pow]
    field_simp
    ring
  rw [hx]
  have h1 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  exact le_mul_of_one_le_left (by positivity) h1

theorem prodDist_step {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s S : Finset ι) (hS : S ⊆ s)
    (h3 : 3 * S.card ≤ s.card) (r ρ : ℝ) (hr : 0 < r)
    (hfar : ∀ j ∈ s, j ∉ S → r / 5 ≤ |ρ - t j|)
    (hin : ((r / 5) / 25) ^ S.card ≤ ∏ j ∈ S, |ρ - t j|) :
    (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  have hsplit : (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| = ∏ j ∈ s, |ρ - t j| :=
    Finset.prod_sdiff hS
  have hfar' : (r / 5) ^ (s \ S).card ≤ ∏ j ∈ s \ S, |ρ - t j| := by
    calc (r / 5) ^ (s \ S).card = ∏ _j ∈ s \ S, (r / 5) := (Finset.prod_const _).symm
      _ ≤ ∏ j ∈ s \ S, |ρ - t j| := by
        apply Finset.prod_le_prod₀
        · intro i _
          positivity
        · intro i hi
          rw [Finset.mem_sdiff] at hi
          exact hfar i hi.1 hi.2
  have hcard : (s \ S).card + S.card = s.card := Finset.card_sdiff_add_card_eq_card hS
  have hka : S.card ≤ (s \ S).card := by omega
  have key := pow_key (r / 25) (by positivity) (s \ S).card S.card hka
  calc (r / 25) ^ s.card = (r / 25) ^ ((s \ S).card + S.card) := by rw [hcard]
    _ ≤ (5 * (r / 25)) ^ (s \ S).card * (r / 25 / 5) ^ S.card := key
    _ = (r / 5) ^ (s \ S).card * ((r / 5) / 25) ^ S.card := by
        rw [show 5 * (r / 25) = r / 5 by ring, show r / 25 / 5 = r / 5 / 25 by ring]
    _ ≤ (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| :=
        mul_le_mul hfar' hin (by positivity)
          (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = ∏ j ∈ s, |ρ - t j| := hsplit

private theorem exists_center_near_with_few_points_close {ι : Type*} (t : ι → ℝ) (s : Finset ι) (c r : ℝ)
    (hr : 0 < r) :
    ∃ c' : ℝ, |c' - c| ≤ 4 * r / 5 ∧
      3 * (s.filter (fun j => |t j - c'| < 2 * r / 5)).card ≤ s.card := by
  classical
  set S1 := s.filter (fun j => |t j - (c - 4 * r / 5)| < 2 * r / 5) with hS1
  set S2 := s.filter (fun j => |t j - c| < 2 * r / 5) with hS2
  set S3 := s.filter (fun j => |t j - (c + 4 * r / 5)| < 2 * r / 5) with hS3
  have d12 : Disjoint S1 S2 := by
    rw [hS1, hS2, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d13 : Disjoint S1 S3 := by
    rw [hS1, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d23 : Disjoint S2 S3 := by
    rw [hS2, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : S1 ∪ S2 ∪ S3 ⊆ s :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have hsum : S1.card + S2.card + S3.card ≤ s.card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12] at h
  by_cases h1 : 3 * S1.card ≤ s.card
  · refine ⟨c - 4 * r / 5, ?_, h1⟩
    rw [abs_le]
    constructor <;> linarith
  by_cases h2 : 3 * S2.card ≤ s.card
  · refine ⟨c, ?_, h2⟩
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨c + 4 * r / 5, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have h3' : 3 * S3.card ≤ s.card := by omega
      exact h3'

theorem exists_far_from_points {ι : Type*} [DecidableEq ι] (t : ι → ℝ) :
    ∀ (N : ℕ) (s : Finset ι), s.card = N → ∀ (c r : ℝ), 0 < r →
      ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hs c r hr
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [Finset.card_eq_zero] at hs
      subst hs
      refine ⟨c, by simp [hr.le], by simp⟩
    · obtain ⟨c', hc', h3⟩ := exists_center_near_with_few_points_close t s c r hr
      set S := s.filter (fun j => |t j - c'| < 2 * r / 5) with hSdef
      have hlt : S.card < N := by omega
      obtain ⟨ρ, hρ, hin⟩ := ih S.card hlt S rfl c' (r / 5) (by positivity)
      refine ⟨ρ, ?_, prodDist_step t s S (Finset.filter_subset _ _) h3 r ρ hr ?_ hin⟩
      · calc |ρ - c| ≤ |ρ - c'| + |c' - c| := abs_sub_le ρ c' c
          _ ≤ r / 5 + 4 * r / 5 := add_le_add hρ hc'
          _ = r := by ring
      · intro j hj hjS
        have hn : 2 * r / 5 ≤ |t j - c'| :=
          not_lt.mp (fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩))
        have htri : |t j - c'| ≤ |t j - ρ| + |ρ - c'| := abs_sub_le (t j) ρ c'
        rw [abs_sub_comm (t j) ρ] at htri
        linarith

theorem prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| :=
  exists_far_from_points t s.card s rfl c r hr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExistsPowerSumLowerBound
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem exists_power_sum_lower_bound (C : ℝ) (a : ℕ) (hC : 0 < C)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ j n : ℕ, m + 1 ≤ j ∧ j ≤ m + a * n ∧ 1 ≤ n ∧ (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re ∧
      (1 / 2) ^ j * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤
        ‖∑ i, u i ^ j‖ + ε ^ (j - 2) * ∑ i, (u i).re := by
  classical
  have hre0 : ∀ i, 0 ≤ (u i).re := fun i => le_trans (sq_nonneg _) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := by
      first
        | exact Complex.re_le_norm (u i)
        | exact Complex.re_le_abs (u i)
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i0, hi0⟩ := hi

  set I := Finset.univ.filter (fun i => ε ≤ ‖u i‖) with hIdef
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
  have hIne : I.Nonempty := ⟨i0, hi0I⟩
  obtain ⟨i1, hi1I, hi1⟩ := Finset.exists_mem_eq_sup' hIne (fun i => ‖u i‖)
  set r := I.sup' hIne (fun i => ‖u i‖) with hr
  have hr0 : 1 / 2 ≤ r := le_trans hi0 (Finset.le_sup' (fun i => ‖u i‖) hi0I)
  have hrpos : 0 < r := by linarith
  have hnr : ‖(r : ℂ)‖ = r := by
    first
      | rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      | simp [abs_of_pos hrpos]
  set n := I.card with hn
  have hn1 : 1 ≤ n := Finset.card_pos.2 hIne
  let e : Fin n ≃ I := I.equivFin.symm
  let z : Fin n → ℂ := fun k => u (e k) / r
  have hz1 : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z]
    rw [norm_div, hnr, div_le_one hrpos]
    exact Finset.le_sup' (fun i => ‖u i‖) (e k).2
  have hz2 : ∃ k, ‖z k‖ = 1 := by
    refine ⟨e.symm ⟨i1, hi1I⟩, ?_⟩
    simp only [z, Equiv.apply_symm_apply]
    rw [norm_div, hnr, ← hi1]
    exact div_self hrpos.ne'
  obtain ⟨k, hk1, hk2, hkB⟩ := hT n m z hn1 hz1 hz2

  have hsumz : ∑ k', z k' ^ k = (∑ i ∈ I, u i ^ k) / (r : ℂ) ^ k := by
    simp only [z, div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [← Finset.sum_coe_sort I]
    exact e.sum_comp (fun i : I => u i ^ k)
  have hB0 : 0 ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hC.le (by positivity))) _
  have hmain : (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i ∈ I, u i ^ k‖ := by
    rw [hsumz, norm_div, norm_pow, hnr, le_div_iff₀ (pow_pos hrpos k)] at hkB
    calc (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n)
        ≤ r ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr0 k) hB0
      _ ≤ ‖∑ i ∈ I, u i ^ k‖ := by linarith

  have hcompl : ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ε ^ (k - 2) * ∑ i, (u i).re := by
    calc ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ∑ i ∈ Iᶜ, ε ^ (k - 2) * (u i).re := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hlt : ‖u i‖ < ε := by
            rw [Finset.mem_compl, Finset.mem_filter] at hi
            push_neg at hi
            exact hi (Finset.mem_univ _)
          calc ‖u i‖ ^ k = ‖u i‖ ^ 2 * ‖u i‖ ^ (k - 2) := by
                rw [← pow_add]
                congr 1
                omega
            _ ≤ (u i).re * ε ^ (k - 2) :=
                mul_le_mul (hu i) (pow_le_pow_left₀ (norm_nonneg _) hlt.le _) (by positivity) (hre0 i)
            _ = ε ^ (k - 2) * (u i).re := by ring
      _ = ε ^ (k - 2) * ∑ i ∈ Iᶜ, (u i).re := by rw [Finset.mul_sum]
      _ ≤ ε ^ (k - 2) * ∑ i, (u i).re :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i)
            (by positivity)
  have hsplit : ‖∑ i ∈ I, u i ^ k‖ ≤ ‖∑ i, u i ^ k‖ + ∑ i ∈ Iᶜ, ‖u i‖ ^ k := by
    have h := Finset.sum_add_sum_compl I (fun i => u i ^ k)
    have h' : ∑ i ∈ I, u i ^ k = ∑ i, u i ^ k - ∑ i ∈ Iᶜ, u i ^ k := by
      rw [← h]
      ring
    rw [h']
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_pow _ _))
  have hnε : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ I, ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (u i).re := Finset.sum_le_sum fun i hi =>
          le_trans (pow_le_pow_left₀ hε0.le (Finset.mem_filter.1 hi).2 2) (hu i)
      _ ≤ ∑ i, (u i).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i
  refine ⟨k, n, hk1, hk2, hn1, hnε, ?_⟩
  linarith [hmain, hsplit, hcompl]

theorem turan_lb (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hCm : 0 < max C 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-(m : ℝ) / n) * (m + n) ≤ n :=
    calc Real.exp (-(m : ℝ) / n) * (m + n) = n * (Real.exp (-(m : ℝ) / n) * ((m : ℝ) / n + 1)) := by
          field_simp
      _ ≤ n * (Real.exp (-(m : ℝ) / n) * Real.exp ((m : ℝ) / n)) := by
          gcongr
          exact Real.add_one_le_exp _
      _ = n := by
          rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  have hb : Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ≤ (n : ℝ) / (C * (m + n)) := by
    rw [Real.exp_sub, Real.exp_log hCm]
    have h2 : Real.exp (-(m : ℝ) / n) ≤ n / (m + n) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc Real.exp (-(m : ℝ) / n) / max C 1 ≤ ((n : ℝ) / (m + n)) / max C 1 := by gcongr
      _ ≤ ((n : ℝ) / (m + n)) / C := by
          gcongr
          exact le_max_left _ _
      _ = n / (C * (m + n)) := by rw [div_div, mul_comm]
  calc Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1))
      = Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ^ (a * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ ((n : ℝ) / (C * (m + n))) ^ (a * n) := pow_le_pow_left₀ (Real.exp_pos _).le hb _

theorem fact_bound (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    x ^ j / ((j - 1).factorial : ℝ) ≤ j * (Real.exp 1 * x / j) ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : (0 : ℝ) < (j : ℝ) ^ j := pow_pos hjpos j
  have hfact : ((j - 1).factorial : ℝ) * j = j.factorial := by
    have : j * (j - 1).factorial = j.factorial := by
      first
        | exact Nat.mul_factorial_pred (show j ≠ 0 by omega)
        | exact Nat.mul_factorial_pred (show 0 < j by omega)
    rw [← this]
    push_cast
    ring
  have hkey : (j : ℝ) ^ j / j.factorial ≤ Real.exp 1 ^ j :=
    calc (j : ℝ) ^ j / j.factorial ≤ Real.exp j := by
          first
            | exact Real.pow_div_factorial_le_exp _ hjpos.le j
            | exact Real.pow_div_factorial_le_exp hjpos.le j
      _ = Real.exp 1 ^ j := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : 1 / (j.factorial : ℝ) ≤ Real.exp 1 ^ j / (j : ℝ) ^ j := by
    rw [div_le_div_iff₀ hF hP]
    rw [div_le_iff₀ hF] at hkey
    linarith
  have hx' : 0 ≤ (j : ℝ) * x ^ j := by positivity
  calc x ^ j / ((j - 1).factorial : ℝ) = ((j : ℝ) * x ^ j) * (1 / j.factorial) := by
        rw [← hfact]
        field_simp
    _ ≤ ((j : ℝ) * x ^ j) * (Real.exp 1 ^ j / (j : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hx'
    _ = j * (Real.exp 1 * x / j) ^ j := by
        rw [div_pow, mul_pow]
        ring

theorem log_sq_bound (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by
  have h3M : (1 : ℝ) ≤ 3 * M := by linarith
  have hL0 : 0 ≤ Real.log (3 * M) := Real.log_nonneg h3M
  have hL : Real.log (3 * M) ≤ (3 * M) ^ ((1 : ℝ) / 4) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (3 * M) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (3 * M) ≤ 2 * Real.sqrt M := by
    rw [← h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log (3 * M) ^ 2 ≤ ((3 * M) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 :=
        pow_le_pow_left₀ hL0 hL 2
    _ = 16 * ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
    _ = 16 * Real.sqrt (3 * M) := by rw [hq]
    _ ≤ 32 * Real.sqrt M := by linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainA
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
  have key : ((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ) : ℝ) : ℂ) := by
    have h1 : ∀ q, ((‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
          (((J n q * J n' q : ℤ) : ℝ) : ℂ) := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      simp only [map_mul, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
  calc (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2)
      ≤ ‖((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; exact le_abs_self _
    _ ≤ ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          RCLike.norm_conj, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc n),
          abs_of_nonneg (hc n')]
        have h2 : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
          have := mul_le_mul (hκ n) (hκ n') (norm_nonneg _) zero_le_one
          simpa using this
        have h3 : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
        have h4 : c n * c n' * (‖κ n‖ * ‖κ n'‖) ≤ c n * c n' := by
          simpa using mul_le_mul_of_nonneg_left h2 h3
        exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainB
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤
      ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) +
        η * (c n * c n')) * P := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    have hAP := mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc
    have hηP : 0 ≤ η * (c n * c n') * P := mul_nonneg (mul_nonneg hη hcc) hP
    have hccP : 0 ≤ c n * c n' * P := mul_nonneg hcc hP
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have hA2 := mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc
      linarith
  calc ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n'
      ≤ ∑ n ∈ I, ∑ n' ∈ I, ((if r n n' = 1 then c n * c n' else 0) +
          (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishB
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]


end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
end
end

