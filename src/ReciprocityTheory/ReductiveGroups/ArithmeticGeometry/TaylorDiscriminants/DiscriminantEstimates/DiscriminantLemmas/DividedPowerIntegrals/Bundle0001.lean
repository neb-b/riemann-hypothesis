module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenDefs
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenPow
section
open MvPolynomial

namespace PI.DivPowInteg.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem pderiv_comm (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have hc : ∀ (c d : I ⊕ J) (n : I ⊕ J),
      pderiv c (Pi.single (M := fun _ => MvPolynomial (I ⊕ J) K) d 1 n) = 0 := by
    intro c d n
    rw [Pi.single_apply]
    split_ifs <;> simp
  induction p using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), hc, hp, mul_zero, zero_add]
    ring

noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap

private theorem gdelta_apply' (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta]

theorem commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  refine LinearMap.ext fun R => ?_
  show gdelta κ (pderiv c R) = pderiv c (gdelta κ R)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gdelta_apply', map_sum, map_smul, Derivation.map_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_comm c (Sum.inl i), pderiv_comm c (Sum.inr j)]

private theorem dL_apply' (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL]

private theorem dR_apply' (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  simp [dR]

private theorem gdelta_pderiv_comm (κ : I → J → K) (c : I ⊕ J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (pderiv c S) = pderiv c (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_pd κ c).eq S

theorem commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dL κ i S) = dL κ i (gdelta κ S)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dL_apply', dL_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

theorem commute_gdelta_dR (κ : I → J → K) (j : J) : Commute (gdelta κ) (dR κ j) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dR κ j S) = dR κ j (gdelta κ S)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dR_apply', dR_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

theorem gdelta_dL_apply (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dL κ i).eq S

theorem gdelta_dR_apply (κ : I → J → K) (j : J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dR κ j S) = dR κ j (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dR κ j).eq S

theorem gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by
  rw [pow_succ']
  rfl

theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  exact gdelta_apply' κ R

theorem dL_apply (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  exact dL_apply' κ i R

theorem dR_apply (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  exact dR_apply' κ j R

theorem gdelta_X_inl (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ j, pderiv (Sum.inr j) (X (Sum.inl i) * R) = X (Sum.inl i) * pderiv (Sum.inr j) R := by
    intro j
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inl_ne_inr, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inl i) * S) =
      X (Sum.inl i) * pderiv (Sum.inl i') S + if i' = i then S else 0 := by
    intro i' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : i' = i
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inl_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have hΔ : ∀ S : MvPolynomial (I ⊕ J) K,
      gdelta κ S = ∑ j, ∑ i', κ i' j • pderiv (Sum.inl i') (pderiv (Sum.inr j) S) := by
    intro S
    rw [gdelta_apply, Finset.sum_comm]
  rw [hΔ, hΔ, dL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, Finset.mul_sum]
  simp only [h2, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem gdelta_X_inr (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inr j) * R) = X (Sum.inr j) * gdelta κ R + dR κ j R := by
  classical
  have h1 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K),
      pderiv (Sum.inl i') (X (Sum.inr j) * S) = X (Sum.inr j) * pderiv (Sum.inl i') S := by
    intro i' S
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inr_ne_inl, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (j' : J) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inr j') (X (Sum.inr j) * S) =
      X (Sum.inr j) * pderiv (Sum.inr j') S + if j' = j then S else 0 := by
    intro j' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : j' = j
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inr_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have h3 : ∀ (i' : I) (j' : J), pderiv (Sum.inl i') (pderiv (Sum.inr j') (X (Sum.inr j) * R)) =
      X (Sum.inr j) * pderiv (Sum.inl i') (pderiv (Sum.inr j') R) +
        if j' = j then pderiv (Sum.inl i') R else 0 := by
    intro i' j'
    rw [h2, map_add (f := _), h1]
    split_ifs <;> simp
  rw [gdelta_apply, gdelta_apply, dR_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.mul_sum]
  simp only [h3, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

theorem powXL_holds : PowXL := by
  unfold PowXL
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add (f := _), map_nsmul, gdelta_X_inl, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

theorem powXR_holds : PowXR := by
  unfold PowXR
  intro K I J _ _ _ κ j R n
  induction n with
  | zero => simp [gdelta_X_inr]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add (f := _), map_nsmul, gdelta_X_inr, gdelta_dR_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]

end

end PI.DivPowInteg.Gen
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.NatMulFactorialBound
section
open MvPolynomial

namespace PI.DivPowInteg.Top

open PI.DivPowInteg.Gen

section

variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]

noncomputable def dpow (κ : I → J → K) (n : ℕ) (R : MvPolynomial (I ⊕ J) K) :
    MvPolynomial (I ⊕ J) K :=
  ((n.factorial : ℚ)⁻¹) • (gdelta κ ^ n) R

theorem dpow_zero (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) : dpow κ 0 R = R := by
  simp [dpow]

theorem dpow_add (κ : I → J → K) (n : ℕ) (p q : MvPolynomial (I ⊕ J) K) :
    dpow κ n (p + q) = dpow κ n p + dpow κ n q := by
  simp [dpow, map_add (f := _), smul_add]

theorem gdelta_C (κ : I → J → K) (c : K) : gdelta κ (C c) = 0 := by
  simp [gdelta]

theorem dpow_C_succ (κ : I → J → K) (k : ℕ) (c : K) : dpow κ (k + 1) (C c) = 0 := by
  rw [dpow, pow_succ, Module.End.mul_apply, gdelta_C, map_zero, smul_zero]

theorem nat_mul_factorial_bound (k : ℕ) :
    ((k + 1).factorial : ℚ)⁻¹ * ((k + 1 : ℕ) : ℚ) = (k.factorial : ℚ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem dpow_X_mul (κ : I → J → K) (s : I ⊕ J)
    (D : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K) (R : MvPolynomial (I ⊕ J) K)
    (k : ℕ)
    (h : (gdelta κ ^ (k + 1)) (X s * R) =
      X s * (gdelta κ ^ (k + 1)) R + (k + 1) • D ((gdelta κ ^ k) R)) :
    dpow κ (k + 1) (X s * R) = X s * dpow κ (k + 1) R + D (dpow κ k R) := by
  unfold dpow
  rw [h, smul_add, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, nat_mul_factorial_bound,
    LinearMap.map_smul_of_tower]

def Good (L : Submodule A K) (n : ℕ) (Q : MvPolynomial (I ⊕ J) K) : Prop :=
  ∀ m, Q.coeff m ∈ L ^ n

theorem good_X_mul (L : Submodule A K) (n : ℕ) (s : I ⊕ J) (Q : MvPolynomial (I ⊕ J) K)
    (hQ : Good L n Q) : Good L n (X s * Q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact hQ _
  · exact Submodule.zero_mem _

theorem good_smul_pderiv (L : Submodule A K) (k : ℕ) (c : K) (hc : c ∈ L) (s : I ⊕ J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) (m : (I ⊕ J) →₀ ℕ) :
    c * (AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1)) ∈ L ^ (k + 1) := by
  have hy : AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1) ∈ L ^ k := by
    have e : AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1) =
        (m s + 1) • AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact nsmul_mem (hQ _) _
  rw [pow_succ']
  exact Submodule.mul_mem_mul hc hy

theorem good_dL (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (i : I)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dL κ i Q) := by
  intro m
  have e : (dL κ i Q).coeff m = ∑ j, κ i j * AddMonoidAlgebra.coeff (pderiv (Sum.inr j) Q) m := by
    simp [dL, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

theorem good_dR (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (j : J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dR κ j Q) := by
  intro m
  have e : (dR κ j Q).coeff m = ∑ i, κ i j * AddMonoidAlgebra.coeff (pderiv (Sum.inl i) Q) m := by
    simp [dR, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

theorem integ (h1 : PowXL) (h2 : PowXR) (L : Submodule A K) (κ : I → J → K)
    (hκ : ∀ i j, κ i j ∈ L) (P : MvPolynomial (I ⊕ J) A) :
    ∀ n, Good L n (dpow κ n (map (algebraMap A K) P)) := by
  classical
  have h0 : ∀ P : MvPolynomial (I ⊕ J) A, Good L 0 (map (algebraMap A K) P) := by
    intro P m
    rw [MvPolynomial.coeff_map, pow_zero]
    exact Submodule.algebraMap_mem _
  refine MvPolynomial.induction_on
    (motive := fun P => ∀ n, Good L n (dpow κ n (map (algebraMap A K) P))) P ?_ ?_ ?_
  · intro a n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (C a)
    | succ k =>
      rw [MvPolynomial.map_C, dpow_C_succ]
      intro m
      rw [MvPolynomial.coeff_zero]
      exact Submodule.zero_mem _
  · intro p q hp hq n m
    rw [map_add (f := _), dpow_add, MvPolynomial.coeff_add]
    exact Submodule.add_mem _ (hp n m) (hq n m)
  · intro p s hp n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (p * X s)
    | succ k =>
      rw [map_mul, MvPolynomial.map_X, mul_comm]
      cases s with
      | inl i =>
        rw [dpow_X_mul κ (Sum.inl i) (dL κ i) (map (algebraMap A K) p) k
          (h1 K I J κ i (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dL L κ hκ k i _ (hp k) m)
      | inr j =>
        rw [dpow_X_mul κ (Sum.inr j) (dR κ j) (map (algebraMap A K) p) k
          (h2 K I J κ j (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dR L κ hκ k j _ (hp k) m)

end

theorem divPowInteg_of (h1 : PowXL) (h2 : PowXR) (h3 : VanL) (h4 : VanR) : PI.DivPowInteg := by
  intro A K I J _ _ _ _ _ _ L κ hκ P n
  have hd : PI.DivPowInteg.delta κ = gdelta κ := rfl
  rw [hd]
  refine ⟨fun m => integ h1 h2 L κ hκ P n m, fun hv => ?_⟩
  rcases hv with hv | hv
  · exact h3 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)
  · exact h4 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)

end PI.DivPowInteg.Top
end

