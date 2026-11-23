module

public import Formalism.IncomingBounds.DefsThmP
public import Formalism.IncomingBounds.FlowDegreeBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.ThmPExp
section
noncomputable section
open scoped BigOperators
open MvPowerSeries Finset

namespace Formalism.IncomingBounds

section ThmPExpLemmas

variable {C : Type} [Field C] {σ : Type}

theorem thmPExp_coeff_pow_eq_zero {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    {m : σ →₀ ℕ} {k : ℕ} (hk : m.degree < k) : coeff m (h ^ k) = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (le_order_pow_of_constantCoeff_eq_zero k hh))

theorem thmPExp_coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {m : σ →₀ ℕ} {j j' : ℕ} (hk : m.degree < j + j') :
    coeff m (a ^ j * b ^ j') = 0 :=
  by
  have h1 := le_order_pow_of_constantCoeff_eq_zero j ha
  have h2 := le_order_pow_of_constantCoeff_eq_zero j' hb
  apply coeff_of_lt_order
  calc ((m.degree : ℕ) : ℕ∞) < ((j + j' : ℕ) : ℕ∞) := by exact_mod_cast hk
    _ = (j : ℕ∞) + (j' : ℕ∞) := by push_cast; rfl
    _ ≤ (a ^ j).order + (b ^ j').order := add_le_add h1 h2
    _ ≤ _ := le_order_mul

theorem thmPExp_coeff_mvExp {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    (m : σ →₀ ℕ) {N : ℕ} (hN : m.degree < N) :
    coeff m (mvExp h) = ∑ k ∈ range N, coeff m (h ^ k) / (k.factorial : C) := by
  change ∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) = _
  apply Finset.sum_subset (range_subset_range.2 (by omega))
  intro k hk hk'
  simp only [mem_range, not_lt] at hk hk'
  rw [thmPExp_coeff_pow_eq_zero hh (by omega), zero_div]

theorem thmPExp_degree_le_of_mem_antidiagonal [DecidableEq σ] {m : σ →₀ ℕ} {pq : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hpq : pq ∈ antidiagonal m) : pq.1.degree ≤ m.degree ∧ pq.2.degree ≤ m.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have := congrArg Finsupp.degree hpq
  rw [map_add (f := _)] at this
  omega

end ThmPExpLemmas

theorem thmPExp_choose_div_factorial {K : Type} [Field K] [CharZero K] {k j : ℕ} (hjk : j ≤ k) :
    ((k.choose j : ℕ) : K) / (k.factorial : K) =
      1 / ((j.factorial : K) * ((k - j).factorial : K)) := by
  have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hjk)
  push_cast at h
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hj : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkj : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff hk (mul_ne_zero hj hkj), one_mul, ← h]
  ring

theorem expSeriesAdd : ExpAdd := by
  intro K _ _ σ a b ha hb
  classical
  ext m
  have hN : m.degree < m.degree + 1 := Nat.lt_succ_self _
  set N := m.degree + 1 with hNdef
  have hab : constantCoeff (a + b) = 0 := by simp [ha, hb]
  have hmid : ∀ F : ℕ → ℕ → K,
      ∑ k ∈ range N, ∑ j ∈ range (k + 1), F j (k - j) =
        ∑ j ∈ range N, ∑ j' ∈ range (N - j), F j j' := by
    intro F
    rw [Finset.sum_comm' (t' := range N) (s' := fun j => Ico j N)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      congr 1
      omega
    · intro k j
      simp only [mem_range, mem_Ico]
      omega
  calc coeff m (mvExp (a + b))
      = ∑ k ∈ range N, coeff m ((a + b) ^ k) / (k.factorial : K) := thmPExp_coeff_mvExp hab m hN
    _ = ∑ k ∈ range N, ∑ j ∈ range (k + 1),
          coeff m (a ^ j * b ^ (k - j)) / ((j.factorial : K) * ((k - j).factorial : K)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [add_pow, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [mem_range] at hj
        rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C, mul_div_assoc,
          thmPExp_choose_div_factorial (by omega), mul_one_div]
    _ = ∑ j ∈ range N, ∑ j' ∈ range (N - j),
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) :=
        hmid (fun j j' => coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)))
    _ = ∑ j ∈ range N, ∑ j' ∈ range N,
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        apply Finset.sum_subset (range_subset_range.2 (by omega))
        intro j' _ hj'
        simp only [mem_range, not_lt] at hj'
        rw [thmPExp_coeff_pow_mul_pow_eq_zero ha hb (by omega), zero_div]
    _ = ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b) := by
        symm
        calc ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b)
            = ∑ pq ∈ antidiagonal m, ∑ j ∈ range N, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := by
              refine Finset.sum_congr rfl (fun pq hpq => ?_)
              rw [thmPExp_coeff_mvExp ha pq.1 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).1; omega),
                thmPExp_coeff_mvExp hb pq.2 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).2; omega),
                Finset.sum_mul_sum]
          _ = ∑ j ∈ range N, ∑ pq ∈ antidiagonal m, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun j' _ => ?_)
              rw [coeff_mul, Finset.sum_div]
              refine Finset.sum_congr rfl (fun pq _ => ?_)
              rw [div_mul_div_comm]
    _ = coeff m (mvExp a * mvExp b) := (coeff_mul _ _ _).symm

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section
variable {C : Type} [Field C]

theorem tpjet_jetAt0_superset {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, AddMonoidAlgebra.coeff P m * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]

private theorem mem_support_or_of_mem_support_add {σ : Type} (P Q : MvPolynomial σ C)
    (a : σ →₀ ℕ) (ha : a ∈ (P + Q).support) : a ∈ P.support ∨ a ∈ Q.support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at ha
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  by_cases hP : AddMonoidAlgebra.coeff P a = 0
  · right
    rwa [hP, zero_add] at ha
  · exact Or.inl hP

theorem tpjet_jetAt0_add {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  have h1 : (P + Q).support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (mem_support_or_of_mem_support_add P Q a ha)
  have h2 : P.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inl ha)
  have h3 : Q.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inr ha)
  rw [tpjet_jetAt0_superset (P + Q) G _ h1, tpjet_jetAt0_superset P G _ h2,
    tpjet_jetAt0_superset Q G _ h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem tpjet_jetAt0_zero {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  unfold jetAt0
  simp

theorem tpjet_jetAt0_sum {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

end
end Formalism.IncomingBounds
end
end

