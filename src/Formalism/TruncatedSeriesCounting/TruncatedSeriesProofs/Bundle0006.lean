module

public import Mathlib
public import Formalism.TruncatedSeriesCounting.Bundle0001

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncSig
section
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncationRemainderBound
section
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.UnitCoefficientPowerMod
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

theorem unit_coefficient_power_mod : UnitCoefficientPowerMod := by
  intro O _ ℓ ε u y
  have hsplit : ∃ W : PowerSeries O,
      (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W := by
    obtain ⟨V, hV⟩ := sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y
    refine ⟨ε * V, ?_⟩
    have : Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε := by unfold Formalism.WindowSums.p1; ring
    rw [this] at hV
    linear_combination hV
  obtain ⟨W, hW⟩ := hsplit
  have hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) =
      constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W := by
    rw [hW, map_add (f := _), coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]
    have := coeff_mul_X_pow (u ^ y) (y * ℓ) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff, map_pow]
  refine ⟨?_, ?_⟩
  · rw [hc, add_sub_cancel_left, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  · intro hloc hℓ hu
    rw [hc]
    have h0 : IsUnit (constantCoeff u ^ y) := (hu.map constantCoeff).pow y
    have h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)
    by_contra hne
    have h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hne
    have h3 := Ideal.sub_mem _ h2 h1
    rw [add_sub_cancel_right] at h3
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) h0

end Formalism.TruncatedSeriesCounting.X
end
end

