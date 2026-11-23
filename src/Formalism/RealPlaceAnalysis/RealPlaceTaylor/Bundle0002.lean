module

public import Formalism.RealPlaceAnalysis.Bundle0001

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
section
open Finset

noncomputable section

namespace Formalism.REAL

theorem iteratedGrowthBound_holds : GrowthIter := by
  intro V _ _ X U B C hB hC hX j k
  induction k generalizing j with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    obtain ⟨hXw, hnorm⟩ := hX j w hw
    have h1 := ih (j + 1) (X w) hXw
    have e : B + ((j + 1 : ℕ) : ℝ) + (k : ℝ) = B + (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    rw [e] at h1
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hBj : 0 ≤ B + (j : ℝ) := by linarith
    have hL : 0 ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hBjL : B + (j : ℝ) ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hCk : 0 ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k := by positivity
    calc ‖(X ^ (k + 1)) w‖ = ‖(X ^ k) (X w)‖ := by rw [pow_succ, Module.End.mul_apply]
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * ‖X w‖ := h1
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * (C * (B + j) * ‖w‖) := by gcongr
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k *
            (C * (B + (j : ℝ) + ((k : ℝ) + 1)) * ‖w‖) := by gcongr
      _ = C ^ (k + 1) * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ (k + 1) * ‖w‖ := by ring

theorem taylorSummable_holds : TaylorRadius := by
  intro C m t hC hm ht h
  have hCt : 0 ≤ C * t := mul_nonneg hC ht
  have hr0 : 0 ≤ C * t * Real.exp 1 := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 h).mul_left (Real.exp m))
  have hx : 0 ≤ m + (k : ℝ) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (m + k) hx k
  have h2 : Real.exp (m + k) = Real.exp m * Real.exp 1 ^ k := by
    rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
  have hCtk : 0 ≤ (C * t) ^ k := pow_nonneg hCt k
  calc (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ)
      = (C * t) ^ k * ((m + k) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ (C * t) ^ k * Real.exp (m + k) := by gcongr
    _ = Real.exp m * (C * t * Real.exp 1) ^ k := by rw [h2]; ring

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
section
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section WDA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}

lemma WDA_sgn_symm (ε : Fin n → Bool) (a b : Fin n) : sgn ε a b = sgn ε b a := by
  unfold sgn; simp only [eq_comm]

lemma WDA_norm (hU : IsUnitary ε E) (a b : Fin n) (x : V) :
    (((‖E a b x‖ ^ 2 : ℝ)) : ℂ) = (sgn ε a b : ℂ) * ⟪x, E b a (E a b x)⟫_ℂ := by
  rw [Complex.ofReal_pow, ← hU a b x (E a b x)]
  exact (inner_self_eq_norm_sq_to_K (E a b x)).symm

lemma WDA_op (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    (2 • CasK ε E - Cas E) = ∑ a, ∑ b, ((sgn ε a b : ℂ)) • (E a b * E b a) := by
  simp only [CasK, Cas, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  unfold sgn
  split_ifs with h
  · simp [two_smul]
  · simp

end WDA

section WDA2

theorem sumOfSquaresIdentity_holds : SumSq := by
  intro V _ _ n ε E w hU
  rw [WDA_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    inner_sum, inner_smul_right]
  simp only [Complex.ofReal_sum]
  simp only [WDA_norm hU]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [WDA_sgn_symm]

end WDA2

end Formalism.REAL
end
end

