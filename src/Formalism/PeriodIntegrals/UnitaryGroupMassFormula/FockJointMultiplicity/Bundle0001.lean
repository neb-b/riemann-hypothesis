module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen
section
open MvPolynomial

noncomputable section

namespace PI.FJMX

section Deriv

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem deriv_prod_eq_zero {ι : Type*} (D : Derivation R A A) (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]
    simp

theorem deriv_pow_eq_zero (D : Derivation R A A) (a : A) (n : ℕ) (h : D a = 0) :
    D (a ^ n) = 0 := by
  rw [D.leibniz_pow, h]; simp

theorem deriv_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (s : Finset ι)
    (f : ι → A) : D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    simp only [smul_eq_mul]
    rw [add_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

theorem deriv_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateCol i (fun k => D (M k i))).det := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, map_zsmul, deriv_finset_prod, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Units.smul_def]
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
  · rw [Matrix.updateCol_self]

theorem deriv_det_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M k i) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M k i) = c * M k i') :
    D M.det = 0 := by
  rw [deriv_det]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | ⟨i', hne, c, hc⟩
  · have : (fun k => D (M k i)) = 0 := funext h0
    rw [this]
    simpa using Matrix.det_updateCol_smul M i (0 : A) 0
  · have : (fun k => D (M k i)) = c • (fun k => M k i') := funext fun k => by simp [hc k]
    rw [this, Matrix.det_updateCol_smul]
    rw [Matrix.det_zero_of_column_eq hne.symm]
    · simp
    · intro k
      simp [Matrix.updateCol_self, Matrix.updateCol_ne hne]

theorem deriv_det_eq_zero_rows {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M i k) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M i k) = c * M i' k) :
    D M.det = 0 := by
  rw [← Matrix.det_transpose]
  exact deriv_det_eq_zero D M.transpose h

end Deriv

section Minor

variable {R : Type*} [CommRing R] {σ : Type*}

def minorPolynomial (R : Type*) [CommRing R] {k : ℕ} (g : Fin k → Fin k → σ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)).det

theorem minorPolynomial_isWeightedHomogeneous {k : ℕ} (g : Fin k → Fin k → σ) (w : σ → ℕ) (u v : Fin k → ℕ)
    (hw : ∀ i j, w (g i j) = u i + v j) :
    IsWeightedHomogeneous w (minorPolynomial R g) (∑ i, u i + ∑ j, v j) := by
  classical
  rw [minorPolynomial, Matrix.det_apply']
  apply IsWeightedHomogeneous.sum
  intro τ _
  have hp : IsWeightedHomogeneous w
      (∏ i, (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)) (τ i) i)
      (∑ i, w (g (τ i) i)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X _ _ _
  have hc : ∑ i, w (g (τ i) i) = ∑ i, u i + ∑ j, v j := by
    simp only [hw, Finset.sum_add_distrib]
    congr 1
    exact Equiv.sum_comp τ u
  rw [hc] at hp
  have h0 : IsWeightedHomogeneous w (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R)) 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R)]
    exact isWeightedHomogeneous_C _ _
  have := h0.mul hp
  rw [zero_add] at this
  exact this

theorem pderiv_eq_zero_of_supported {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    {v : σ} (hv : v ∉ S) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hv ((mem_supported.1 hf) h)

end Minor

end PI.FJMX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurChain
section
noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem sum_aeval_pderiv_X_mul_derivation {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B)
    (φ : σ → B) (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (w : σ) :
    ∑ v ∈ S, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) = D (φ w) := by
  classical
  have key : ∀ v, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
      if w = v then D (φ v) else 0 := by
    intro v
    rw [pderiv_X]
    by_cases h : w = v
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hS w h).symm

theorem deriv_aeval {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B) (φ : σ → B)
    (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (f : MvPolynomial σ R) :
    D (aeval φ f) = ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) := by
  classical
  induction f using MvPolynomial.induction_on
  · rename_i a
    simp [aeval_C]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  · rename_i p w hp
    have h1 : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := by
      intro v
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    simp only [h1, map_add (f := _), map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    have h2 : ∑ v ∈ S, aeval φ p * aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
        aeval φ p * D (φ w) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_aeval_pderiv_X_mul_derivation D φ S hS w]
    have h3 : ∑ v ∈ S, aeval φ (pderiv v p) * φ w * D (φ v) =
        φ w * ∑ v ∈ S, aeval φ (pderiv v p) * D (φ v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h2, h3, ← hp]
    ring

theorem aeval_translate_eq {K : Type*} [Field K] [CharZero K] [Algebra R K] (f : MvPolynomial σ R)
    (S : Finset σ) (c : σ → MvPolynomial σ R) (hf : ∑ v ∈ S, c v * pderiv v f = 0) (y z : σ → K)
    (hz : ∀ v, v ∉ S → z v = 0)
    (hc : ∀ v ∈ S, aeval (fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)) (c v) =
      Polynomial.C (z v)) (t : K) :
    aeval (fun w => y w + t * z w) f = aeval y f := by
  classical
  set φ : σ → Polynomial K := fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)
    with hφ
  let D : Derivation R (Polynomial K) (Polynomial K) :=
    (Polynomial.derivative' : Derivation K (Polynomial K) (Polynomial K)).restrictScalars R
  have hD : ∀ q, D q = Polynomial.derivative q := fun q => rfl
  have hDφ : ∀ v, D (φ v) = Polynomial.C (z v) := by
    intro v
    rw [hD, hφ]
    simp
  have hS : ∀ v, v ∉ S → D (φ v) = 0 := by
    intro v hv
    rw [hDφ, hz v hv, map_zero]
  have hder : Polynomial.derivative (aeval φ f) = 0 := by
    rw [← hD, deriv_aeval D φ S hS f]
    calc ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) = ∑ v ∈ S, aeval φ (c v * pderiv v f) := by
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rw [hDφ, map_mul, ← hc v hv, mul_comm]
      _ = aeval φ (∑ v ∈ S, c v * pderiv v f) := by rw [map_sum]
      _ = 0 := by rw [hf, map_zero]
  have hconst : aeval φ f = Polynomial.C ((aeval φ f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder)
  have heval : ∀ (s : K) (g : MvPolynomial σ R),
      (aeval φ g).eval s = aeval (fun w => y w + s * z w) g := by
    intro s g
    induction g using MvPolynomial.induction_on
    · rename_i a
      simp [aeval_C, Polynomial.algebraMap_apply]
    · rename_i p q hp hq
      simp only [map_add (f := _), Polynomial.eval_add, hp, hq]
    · rename_i p n hp
      rw [map_mul, aeval_X, Polynomial.eval_mul, hp, map_mul, aeval_X]
      congr 1
      simp only [hφ, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have h0 : (aeval φ f).eval 0 = aeval y f := by
    have hy : (fun w => y w + 0 * z w) = y := by
      funext w
      simp
    rw [heval 0 f, hy]
  rw [← heval t f, ← h0, hconst, Polynomial.eval_C, Polynomial.eval_C]

end PI.FJMB
end
end

