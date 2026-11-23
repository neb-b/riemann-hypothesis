module

public import Formalism.EisensteinCokernelLengths.RationalTailBound
public import Formalism.EisensteinCokernelLengths.Bundle0001
public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
public import Formalism.WindowSums.PowerSeriesRelationList

@[expose] public section

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.GaussRam
section
open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

private theorem le_addVal_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (hc : c ∈ Ideal.span {ϖ ^ e}) : (e : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  rw [Ideal.mem_span_singleton] at hc
  have h := (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc
  rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one] at h

private theorem addVal_eq_of_mem_span_pow_not_mem_succ {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (h1 : c ∈ Ideal.span {ϖ ^ e}) (h2 : c ∉ Ideal.span {ϖ ^ (e + 1)}) :
    IsDiscreteValuationRing.addVal O c = e := by
  refine le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)
  by_contra h
  rw [not_le] at h
  apply h2
  rw [Ideal.mem_span_singleton]
  apply (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_succ]
  exact Order.add_one_le_of_lt h

theorem gaussValEisenstein : GaussEisRam := by
  intro O _ _ _ ϖ hϖ e he x hx E N hN hE
  obtain ⟨hmon, hdeg, hcoef, h0⟩ := hE
  have hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e :=
    addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0
  have hcN : E.coeff N = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  unfold Formalism.NOK.gaussV
  simp only [Polynomial.coeff_coe]
  apply le_antisymm
  · have h1 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) 0
    have h2 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) N
    simp only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe,
      Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2
    rcases le_total (e : ℝ) (x * N) with h | h
    · rw [min_eq_left h, ENNReal.ofReal_natCast]
      exact h1
    · rw [min_eq_right h]
      exact h2
  · apply le_iInf
    intro n
    rcases lt_trichotomy n N with h | h | h
    · have hv := le_addVal_of_mem_span_pow hϖ (hcoef n h)
      calc ENNReal.ofReal (min (e : ℝ) (x * N)) ≤ ENNReal.ofReal (e : ℝ) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ((e : ℕ∞) : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
        _ ≤ ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hv
        _ ≤ _ := le_self_add
    · subst h
      rw [hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]
      simp

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LagrangeIdealSgProof
section
namespace Formalism.ZetaNonvanishing.LIFTV

theorem lagrangeIdealSg_proof : LagrangeIdealSg := by
  intro ℓ _ R _ _ sg S₁ S₂ c hd hc
  exact Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc

end Formalism.ZetaNonvanishing.LIFTV
end

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.RationalTailBoundCubic
section
noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

theorem exponentChainBound : ExponentChainBound := by
  unfold ExponentChainBound
  intro ℓ b b' S E lam σ₂ h'' c' hℓ hb hS hE hσ hlam hc
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key : b / (ℓ - 1) - b / ℓ = b / (ℓ * (ℓ - 1)) := by
    field_simp; ring
  have hS1 : (S + 1) / (ℓ - 1) ≤ S + 1 := div_le_self (by linarith) (by linarith)
  have hsplit : ((b + S) + 1) / (ℓ - 1) = b / (ℓ - 1) + (S + 1) / (ℓ - 1) := by ring
  have hnn : 0 ≤ b / (ℓ * (ℓ - 1)) := div_nonneg hb (mul_pos h0 h1).le
  apply max_le
  · linarith
  · linarith

lemma numC_cubic (ℓ : ℝ) (hℓ : 11 ≤ ℓ) :
    8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2 ≤ 3111 / 100 * (ℓ - 1) ^ 3 := by
  have ht : 0 ≤ ℓ - 11 := by linarith
  nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]

theorem rationalTailBoundCubic : NumC := by
  unfold NumC
  intro ℓ hℓ
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key := numC_cubic ℓ hℓ
  have e : 8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) =
      (8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2) / (ℓ ^ 2 * (ℓ - 1) ^ 3) := by
    field_simp
  have c : (31.11 : ℝ) = 3111 / 100 := by norm_num
  rw [e, div_le_div_iff₀ (mul_pos (pow_pos h0 2) (pow_pos h1 3)) (pow_pos h0 2), c]
  nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg ℓ)]

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end
end

