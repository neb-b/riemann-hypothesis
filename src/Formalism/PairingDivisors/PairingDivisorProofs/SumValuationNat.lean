module

public import Mathlib
public import Formalism.PairingDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

namespace Formalism.PairingDivisionLocalBalance

theorem vw_prod {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) {P : Type} (R : Finset P)
    (e : P → K) (he : ∀ q ∈ R, e q ≠ 0) : vw w (∏ q ∈ R, e q) = ∑ q ∈ R, vw w (e q) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (he a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun q hq => he q (Finset.mem_insert_of_mem hq)),
      ih fun q hq => he q (Finset.mem_insert_of_mem hq)]

theorem sum_valuation_nat : SumValNat := by
  intro K _ _ _ _ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Formalism.DivisionValues.ValuationRepresentative.vw_zero]
  · have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨h1, h2⟩ := Formalism.DivisionValues.prod_formula' K (n : K) hn0
    refine ⟨h1, ?_⟩
    rw [← h2]
    have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
      have h3 := IsTotallyComplex.finrank K
      have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [h3, h4, h5]; push_cast; ring
    have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hc]
    have : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hc; linarith
    field_simp

end Formalism.PairingDivisionLocalBalance
