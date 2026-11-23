module

public import Mathlib

@[expose] public section

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial

theorem gram_vanish {σ ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (f : ι → MvPolynomial σ ℤ) (ph : MvPolynomial σ K →ₗ[K] K)
    (h : ∑ i, ph (map (Int.castRingHom K) (f i)) • map (Int.castRingHom K) (f i) = 0)
    (i : ι) : ph (map (Int.castRingHom K) (f i)) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ι → MvPolynomial σ K, ∀ j, g j = map (Int.castRingHom K) (f j) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hg] at h ⊢
  have key : ∀ l : Module.Dual ℚ K, ∀ j, l (ph (g j)) = 0 := by
    intro l
    have lin : ∀ (x : K) (n : ℤ), algebraMap ℚ K (l x) * (n : K) = algebraMap ℚ K (l (x * n)) := by
      intro x n
      rw [show x * (n : K) = n • x by rw [zsmul_eq_mul, mul_comm], map_zsmul, zsmul_eq_mul,
        map_mul, map_intCast, mul_comm]
    have hrel : ∑ j, algebraMap ℚ K (l (ph (g j))) • g j = 0 := by
      ext s
      have hs := congrArg (fun p => l (AddMonoidAlgebra.coeff p s)) h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coeff_sum, coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_sum, map_zero] at hs
      have e : ∀ j, AddMonoidAlgebra.coeff (g j) s = ((AddMonoidAlgebra.coeff (f j) s : ℤ) : K) := fun j => by
        rw [hg, coeff_map, eq_intCast]
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      simp only [coeff_smul, smul_eq_mul]
      calc ∑ j, algebraMap ℚ K (l (ph (g j))) * AddMonoidAlgebra.coeff (g j) s
          = ∑ j, algebraMap ℚ K (l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [e j, lin]
        _ = algebraMap ℚ K (∑ j, l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by rw [map_sum]
        _ = 0 := by rw [hs, map_zero]
    have hsum : ∑ j, l (ph (g j)) ^ 2 = 0 := by
      have h1 : l (ph (∑ j, algebraMap ℚ K (l (ph (g j))) • g j)) = 0 := by
        rw [hrel, map_zero, map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul, sq]
    intro j
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ l (ph (g k)) ^ 2 := fun k _ => sq_nonneg _
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ j)
    exact (pow_eq_zero_iff two_ne_zero).mp hj
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (ph (g i))).mp (fun l => key l i)

end PI.WwInjectiveWork
