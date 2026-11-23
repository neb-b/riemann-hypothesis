module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.ChainRule
section
open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

section

variable {K : Type} [Field K] {k : ℕ}

theorem RE_add (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f + g) = RE K k a b f + RE K k a b g := by
  simp only [PI.RL.RE, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem RE_C (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  simp [PI.RL.RE]

private theorem pderiv_mul_eq {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPolynomial σ R) :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

theorem RE_mul (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  simp only [PI.RL.RE, pderiv_mul_eq, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> (refine Finset.sum_congr rfl (fun t _ => ?_); ring)

end

private theorem pderiv_X_eq_ite {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (c i : σ) :
    pderiv c (X i : MvPolynomial σ R) = if c = i then 1 else 0 := by
  rw [pderiv_X]
  by_cases h : c = i
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]

private theorem derivation_aeval_eq_sum_pderiv {K : Type*} [CommRing K] {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    (D : MvPolynomial τ K → MvPolynomial τ K)
    (hadd : ∀ f g, D (f + g) = D f + D g) (hC : ∀ r, D (C r) = 0)
    (hmul : ∀ f g, D (f * g) = D f * g + f * D g)
    (g : σ → MvPolynomial τ K) (P : MvPolynomial σ K) :
    D (aeval g P) = ∑ c, aeval g (pderiv c P) * D (g c) := by
  induction P using MvPolynomial.induction_on
  next r =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, hC]
    simp
  next p q hp hq =>
    rw [map_add (f := _), hadd, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_add (f := _), map_add (f := _), add_mul]
  next p i ih =>
    have e : ∀ c, aeval g (pderiv c (p * X i)) * D (g c) =
        g i * (aeval g (pderiv c p) * D (g c)) + (if c = i then aeval g p * D (g i) else 0) := by
      intro c
      rw [pderiv_mul_eq, pderiv_X_eq_ite, map_add (f := _), map_mul, map_mul, aeval_X]
      by_cases h : c = i
      · subst h; rw [if_pos rfl, if_pos rfl, map_one]; ring
      · rw [if_neg h, if_neg h, map_zero]; ring
    rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_add_distrib, ← Finset.mul_sum, ← ih,
      map_mul, aeval_X, hmul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem chainRule : ChainRule := by
  intro K _ m vec a b P
  simp only [PI.RL.theta]
  exact derivation_aeval_eq_sum_pderiv (PI.RL.RE K (m + 1) a b) (RE_add a b) (RE_C a b)
    (RE_mul a b) _ P

theorem vecX : VecX := by
  intro K _ m a b c
  have hp : ∀ t : Fin (m + 1),
      pderiv (b, t) (X (c, 0) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) =
        if c = b ∧ t = 0 then 1 else 0 := by
    intro t
    rw [pderiv_X]
    by_cases h : c = b ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, Pi.single_apply, if_neg]
      intro he
      simp only [Prod.mk.injEq] at he
      exact h ⟨he.1, he.2.symm⟩
  simp only [PI.RL.Nv, if_true, PI.RL.RE, hp, mul_ite, mul_one, mul_zero]
  by_cases h : c = b
  · subst h; simp [Finset.sum_ite_eq']
  · simp [h]

theorem hdHom : HdHom := by
  intro K _ k d P hP
  unfold PI.RL.Hd at hP
  rw [mem_restrictSupport_iff] at hP
  intro μ hμ
  have h2 := hP (mem_support_iff.mpr hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simpa using h2

end PI.RL.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.NvFalseEq
section
open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

theorem Nv_false_eq (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by
  simp [Nv, Matrix.adjugate_apply]

theorem keyCov : KeyCov := by
  intro K _ m a b c
  have hN : ∀ d, Nv K m false d =
      ((genM K m).updateRow d (Pi.single (Fin.last m) 1)).det := fun d => Nv_false_eq K m d
  have hG : ∀ i j, genM K m i j = X (i, j) := fun i j => rfl
  rw [RE_eq_REder, hN c, hN b, derivation_det]
  have hrow : ∀ i j, REder K (m + 1) a b
      (((genM K m).updateRow c (Pi.single (Fin.last m) 1)) i j) =
        if i = c then 0 else if i = b then X (a, j) else 0 := by
    intro i j
    by_cases hic : i = c
    · subst hic
      rw [Matrix.updateRow_self, if_pos rfl]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · rw [Matrix.updateRow_ne hic, hG, REder_X, if_neg hic]
  simp_rw [hrow]
  have hz : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (i : Fin (m + 1)) (r : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      (∀ j, r j = 0) → (M.updateRow i r).det = 0 := by
    intro M i r hr
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [Matrix.updateRow_self]; exact hr j)
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      apply hz
      intro j
      split_ifs <;> rfl
  rw [Finset.sum_eq_single b]
  rotate_left
  · intro i _ hib
    apply hz
    intro j
    split_ifs <;> rfl
  · intro h; exact absurd (Finset.mem_univ b) h
  simp only [hbc, if_false, if_true, eq_self_iff_true, ite_true, ite_false]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg hbc, sub_zero]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = a
    · rw [hi, Matrix.updateRow_self]
      simp only [Matrix.updateRow_apply, hG]
      try (split_ifs <;> simp_all)
    · rw [Matrix.updateRow_ne hi]
  rw [if_neg hab]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, zero_sub]
    have hperm : (((genM K m).updateRow a (Pi.single (Fin.last m) 1)).updateRow b
        (fun j => X (a, j))) =
        ((genM K m).updateRow b (Pi.single (Fin.last m) 1)).submatrix (Equiv.swap b a) id := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.submatrix_apply, id, Matrix.updateRow_apply, Equiv.swap_apply_def, hG]
      split_ifs <;> simp_all
    rw [hperm, Matrix.det_permute, Equiv.Perm.sign_swap hbc]
    simp
  · rw [if_neg hac, sub_zero]
    apply Matrix.det_zero_of_row_eq hab
    funext j
    rw [Matrix.updateRow_ne hab, Matrix.updateRow_self, Matrix.updateRow_ne hac, hG]

end PI.RL.W
end
end

