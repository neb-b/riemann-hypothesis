module

public import Formalism.PolynomialDimension.Bundle0003

@[expose] public section

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.DvdPowOfNotPowSuccDvd
section
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.CountingSumsFrames

theorem one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by
  classical
  have hP : ∀ t : Finset ι, 1 - ∑ j ∈ t, κ j ≤ ∏ j ∈ t, (1 - κ j) := by
    intro t
    refine Finset.induction_on t (by simp) ?_
    intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ 1 - κ i := by linarith [(hκ i).2]
    have h2 : 0 ≤ ∑ j ∈ t, κ j := Finset.sum_nonneg fun j _ => (hκ j).1
    have h3 := mul_le_mul_of_nonneg_left ih h1
    nlinarith [mul_nonneg (hκ i).1 h2]
  have hd0 : 0 ≤ ∏ j ∈ s, d j := Finset.prod_nonneg fun j _ => hd j
  calc (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ (∏ j ∈ s, (1 - κ j)) * ∏ j ∈ s, d j :=
        mul_le_mul_of_nonneg_right (hP s) hd0
    _ = ∏ j ∈ s, ((1 - κ j) * d j) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ j ∈ s, n j := Finset.prod_le_prod₀
        (fun j _ => mul_nonneg (by linarith [(hκ j).2]) (hd j)) (fun j _ => h j)

theorem share_product_bound : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h

section Partner

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Partner

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.SegmentBoundThreeHolds
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem det_leading_diagonal : DetLeadDiag := by
  intro K _ n J A d hdeg hcoeff
  have hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, A (σ i) i).coeff (n * J) = ∏ i, (A (σ i) i).coeff J := by
    intro σ
    have h1 := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => A (σ i) i) J
      (fun i _ => hdeg (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  rw [Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_intCast, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : Fin n, J := Finset.sum_le_sum fun i _ => hdeg (σ i) i
      _ = n * J := by simp
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
    · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hcoeff]; simp
    · intro σ _ hσ
      rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.ext hσ)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hcoeff, if_neg (by simpa using hi)]), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end Formalism.CountingSumsFrames
end
end

