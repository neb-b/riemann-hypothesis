module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer
section
open MvPolynomial

noncomputable section

namespace PI.RL.W

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem derivation_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R S S) (f : ι → S) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
  have h0 : Function.update f a (D (f a)) a = D (f a) := by simp
  have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j :=
    Finset.prod_congr rfl fun j hj => Function.update_of_ne (hne j hj) _ _
  have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
      f a * ∏ j ∈ s, Function.update f i (D (f i)) j := fun i hi => by
    rw [Finset.prod_insert ha, Function.update_of_ne (hne i hi).symm]
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha, h0, h1,
    Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
  ring

theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R S S) (A : Matrix n n S) :
    D A.det = ∑ i, (A.updateRow i fun j => D (A i j)).det := by
  have key : ∀ B : Matrix n n S, B.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, B i (σ i) :=
    fun B => by rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
  have hc : ∀ k : ℤ, D (k : S) = 0 := fun k => by
    rw [← map_intCast (algebraMap R S) k, Derivation.map_algebraMap]
  have hrow : ∀ (i : n) (σ : Equiv.Perm n), ∏ j, (A.updateRow i fun j => D (A i j)) j (σ j) =
      ∏ j, Function.update (fun j => A j (σ j)) i (D (A i (σ i))) j := fun i σ =>
    Finset.prod_congr rfl fun j _ => by
      by_cases h : j = i
      · subst h; simp
      · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp_rw [key, hrow, Derivation.leibniz, hc, smul_zero, add_zero, derivation_finset_prod, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem derivation_sum_apply {ι : Type*} {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
    [Algebra R A] [Module R M] (s : Finset ι) (D : ι → Derivation R A M) (x : A) :
    (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

end General

def REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) :
    Derivation K (MvPolynomial (Fin k × Fin k) K) (MvPolynomial (Fin k × Fin k) K) :=
  ∑ t : Fin k, (X (a, t) : MvPolynomial (Fin k × Fin k) K) • pderiv (b, t)

theorem RE_eq_REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    PI.RL.RE K k a b f = REder K k a b f := by
  unfold PI.RL.RE REder
  rw [derivation_sum_apply]
  rfl

theorem REder_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (i j : Fin k) :
    REder K k a b (X (i, j)) = if i = b then X (a, j) else 0 := by
  unfold REder
  rw [derivation_sum_apply]
  simp only [Derivation.smul_apply, pderiv_X, smul_eq_mul]
  by_cases h : i = b
  · subst h
    simp [Pi.single_apply, mul_ite]
  · simp [Pi.single_apply, h]

end PI.RL.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development
section
open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

def ChainRule : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (a b : Fin (m + 1)) (P : MvPolynomial (Fin (m + 1)) K),
    RE K (m + 1) a b (theta K m vec P) =
      ∑ c, theta K m vec (pderiv c P) * RE K (m + 1) a b (Nv K m vec c)

def VecX : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0

def KeyCov : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m false c) =
      (if a = b then Nv K m false c else 0) - (if a = c then Nv K m false b else 0)

def HdHom : Prop :=
  ∀ (K : Type) [Field K] (k d : ℕ) (P : MvPolynomial (Fin k) K), P ∈ Hd K k d → P.IsHomogeneous d

theorem theta_X (K : Type) [Field K] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    theta K m vec (X c) = Nv K m vec c := by
  simp [theta]

theorem euler_theta (hH : HdHom) (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ)
    (P : MvPolynomial (Fin (m + 1)) K) (hP : P ∈ Hd K (m + 1) d) :
    ∑ c, theta K m vec (pderiv c P) * Nv K m vec c = (d : K) • theta K m vec P := by
  have h1 := (hH K (m + 1) d P hP).sum_X_mul_pderiv
  have h2 := congrArg (theta K m vec) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, theta_X, map_nsmul] at h2
  rw [← Nat.cast_smul_eq_nsmul K] at h2
  rw [← h2]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

theorem rowLetter_of (hC : ChainRule) (hV : VecX) (hK : KeyCov) (hH : HdHom) : PI.RowLetter := by
  intro K _ m vec d a b P hP
  rw [hC K m vec a b P]
  cases vec
  · have hE := euler_theta hH K m false d P hP
    by_cases hab : a = b
    · subst hab
      have hL : ∑ c, theta K m false (pderiv c P) * RE K (m + 1) a a (Nv K m false c) =
          ∑ c, theta K m false (pderiv c P) * Nv K m false c -
            theta K m false (pderiv a P) * Nv K m false a := by
        have hc : ∀ c, RE K (m + 1) a a (Nv K m false c) =
            Nv K m false c - (if a = c then Nv K m false a else 0) := by
          intro c
          rw [hK K m a a c]
          simp
        simp only [hc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [hL, hE]
      simp only [TE, Bool.false_eq_true, if_true, if_false, map_sub, map_smul, map_mul, theta_X]
      rw [mul_comm (Nv K m false a)]
    · have hc : ∀ c, RE K (m + 1) a b (Nv K m false c) =
          -(if a = c then Nv K m false b else 0) := by
        intro c
        rw [hK K m a b c]
        simp [hab]
      simp only [hc, mul_neg, mul_ite, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp [TE, hab, theta_X] <;> ring
  · have hc : ∀ c, RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0 :=
      fun c => hV K m a b c
    simp only [hc, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [TE, if_true, map_mul, theta_X]
    rw [mul_comm]

end PI.RL.W
end
end

