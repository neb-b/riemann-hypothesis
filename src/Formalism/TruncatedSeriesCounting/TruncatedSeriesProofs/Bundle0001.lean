module

public import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelC
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_C_pow_mul : CancelC := by
  intro O _ _ a v t b g ha hvt hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨p, q, hpq⟩ := hg
  have hdiv : (X : PowerSeries O) ^ b ∣ g - p * C (a ^ (t - v)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have h1 := congrArg (PowerSeries.coeff n) hpq
    simp only [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      if_neg (show ¬ b ≤ n by omega), add_zero] at h1
    rw [map_sub, PowerSeries.coeff_mul_C, sub_eq_zero]
    apply mul_left_cancel₀ (pow_ne_zero v ha)
    rw [← h1]
    have ht : a ^ t = a ^ v * a ^ (t - v) := by rw [← pow_add, Nat.add_sub_cancel' hvt]
    rw [ht]
    ring
  obtain ⟨r, hr⟩ := hdiv
  exact ⟨p, r, by linear_combination (-1 : PowerSeries O) * hr⟩

end Formalism.TruncatedSeriesCounting.R9
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelQ
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_X_pow_mul : CancelQ := by
  intro O _ _ a η b g hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨F, G, hFG⟩ := hg
  have hX : (X : PowerSeries O) ^ η ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, G, ?_⟩
    have h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g := by
      rw [← hFG, map_zero, mul_zero, zero_add, pow_add]
      ring
    rw [zero_mul, zero_add]
    exact mul_left_cancel₀ hX h1
  · have hdvd : (X : PowerSeries O) ^ η ∣ F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h1 : (X : PowerSeries O) ^ η ∣ F * C a := by
        have h0 : F * C a = X ^ η * (g - G * X ^ b) := by
          rw [mul_sub, ← hFG, pow_add]
          ring
        rw [h0]
        exact dvd_mul_right _ _
      rw [PowerSeries.X_pow_dvd_iff] at h1
      have h2 := h1 m hm
      rw [mul_comm, PowerSeries.coeff_C_mul] at h2
      exact (mul_eq_zero.mp h2).resolve_left ha
    obtain ⟨F', rfl⟩ := hdvd
    refine ⟨F', G, ?_⟩
    apply mul_left_cancel₀ hX
    rw [← hFG, pow_add]
    ring

end Formalism.TruncatedSeriesCounting.R9
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero
section
namespace Formalism.TruncatedSeriesCounting.R9

theorem pow_mem_span_pow_mul : TruncZero := by
  intro R _ u π₀ q ℓ M η y hM hη
  rw [Ideal.mem_span_singleton']
  refine ⟨u ^ y * π₀ ^ (y - M) * q ^ ((ℓ - 1) * y - η), ?_⟩
  have h1 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M := by rw [← pow_add, Nat.sub_add_cancel hM]
  have h2 : q ^ ((ℓ - 1) * y) = q ^ ((ℓ - 1) * y - η) * q ^ η := by
    rw [← pow_add, Nat.sub_add_cancel hη]
  rw [mul_pow, mul_pow, ← pow_mul, h1, h2]
  ring

end Formalism.TruncatedSeriesCounting.R9
end

