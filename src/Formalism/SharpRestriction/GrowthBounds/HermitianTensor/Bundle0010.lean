module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0009
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DPsiMonomialIwh
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem rowA_of_iwh {K : Type} [CommRing K] {k n : ℕ} {f : MvPolynomial (Fin k × Fin n) K} {μ : Fin k → ℕ}
    (h : IsWeightedHomogeneous (rowW k n) f μ) (a : Fin k) : RowA a f (μ a) := by
  intro u hu
  rw [← ldrow_weight_rowW, h hu]

theorem qt_cnt (m : ℕ) (i a' : Fin (m + 1)) :
    (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ)) a' = if a' = i then 0 else 1 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · subst h
    exact Finset.sum_eq_zero fun p _ => if_neg (Fin.succAbove_ne a' p).symm
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro p _ hp
      exact if_neg fun e => hp (Fin.succAbove_right_injective e).symm
    · intro hq
      exact absurd (Finset.mem_univ q) hq

theorem qt_covY_iwh (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (covY K m i) (∑ p : Fin m, Pi.single (i.succAbove p) 1) := by
  have e : covY K m i = ((-1 : ℤ) ^ (i : ℕ)) • initMinor K (n := m + 1) i.succAbove (Nat.le_succ m) := by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  rw [e, ← mem_weightedHomogeneousSubmodule]
  exact zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_initMinor_rowHom K i.succAbove (Nat.le_succ m))) _

theorem dPsi_monomial (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    deltaB K m (PsiXY K m (monomial v c)) =
      C c * ((∏ i : Fin (m + 1), X (i, (0 : Fin (m + 1))) ^ v (Sum.inl i)) * ∏ i : Fin (m + 1), covY K m i ^ v (Sum.inr i)) := by
  have hx : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inr i))) = covY K m i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
    rw [this, rename_id_apply]
  have hC : deltaB K m (PsiXY K m (C c)) = C c := by
    simp only [← algebraMap_eq, AlgHom.commutes]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, hC]

def qtW (m : ℕ) (v : XY (m + 1) →₀ ℕ) : Fin (m + 1) → ℕ :=
  0 + ((∑ i : Fin (m + 1), v (Sum.inl i) • (Pi.single i 1 : Fin (m + 1) → ℕ)) +
    ∑ i : Fin (m + 1), v (Sum.inr i) • ∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ))

theorem dPsi_monomial_iwh (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (deltaB K m (PsiXY K m (monomial v c))) (qtW m v) := by
  rw [dPsi_monomial]
  refine (isWeightedHomogeneous_C _ c).mul (IsWeightedHomogeneous.mul ?_ ?_)
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (isWeightedHomogeneous_X K (rowW (m + 1) (m + 1)) (i, 0)).pow _
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (qt_covY_iwh K m i).pow _

theorem qtW_apply (m : ℕ) (v : XY (m + 1) →₀ ℕ) (a' : Fin (m + 1)) :
    qtW m v a' + v (Sum.inr a') = v (Sum.inl a') + yDeg v := by
  classical
  unfold qtW yDeg
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∑ i : Fin (m + 1), v (Sum.inl i) * (Pi.single i 1 : Fin (m + 1) → ℕ) a' = v (Sum.inl a') := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∀ i : Fin (m + 1), (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ) a') = if a' = i then 0 else 1 := by
    intro i
    rw [← Finset.sum_apply]
    exact qt_cnt m i a'
  have h3 : v (Sum.inr a') = ∑ i : Fin (m + 1), v (Sum.inr i) * (if a' = i then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, add_assoc]
  congr 1
  simp only [h2]
  conv_lhs => rw [h3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubCoeffP
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end
end

