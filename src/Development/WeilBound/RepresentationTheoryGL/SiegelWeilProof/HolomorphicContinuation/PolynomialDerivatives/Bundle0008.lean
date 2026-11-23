module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MonomialMemSupported
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem monomial_mem_supported' {S : Set (Fin m × Fin n × Bool)} (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, k ∈ S) (a : ℂ) : (monomial s a : PX m n) ∈ supported ℂ S := by
  by_cases ha : a = 0
  · rw [ha, monomial_zero]; exact Subalgebra.zero_mem _
  · rw [mem_supported, vars_monomial ha]
    intro k hk
    exact hs k hk

theorem box_le_first_family (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : box ε R ≤ F1 (n := n) ε := by
  unfold box
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, -, rfl⟩
  exact monomial_mem_supported' s hs 1

theorem first_family_le_box (ε : Fin m → Bool) : F1 (n := n) ε ≤ box ε Set.univ := by
  intro p hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hF : ∀ k ∈ s.support, inF1 ε k := by
    intro k hk
    have : k ∈ p.vars := by
      rw [MvPolynomial.mem_vars_iff_mem_support]; exact ⟨s, hs, hk⟩
    exact (mem_supported.mp hp) this
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hF, Set.mem_univ _, rfl⟩)

theorem box_mono (ε : Fin m → Bool) {R R' : Set (Fin m → ℕ)} (h : R ⊆ R') : box (n := n) ε R ≤ box ε R' := by
  unfold box
  refine Submodule.span_mono ?_
  rintro _ ⟨s, hs, hr, rfl⟩
  exact ⟨s, hs, h hr, rfl⟩

theorem box_finiteDimensional (ε : Fin m → Bool) (R : Finset (Fin m → ℕ)) :
    FiniteDimensional ℂ (box (n := n) ε (R : Set (Fin m → ℕ))) := by
  classical
  set M : ℕ := R.sup fun r => ∑ a, r a
  have hfin : {p : PX m n | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ (R : Set _) ∧
      p = monomial s 1}.Finite := by
    refine ((Set.finite_univ (α := Fin m × Fin n × Bool → Fin (M + 1))).image
      fun f => (monomial (Finsupp.equivFunOnFinite.symm fun k => (f k : ℕ)) 1 : PX m n)).subset ?_
    rintro _ ⟨s, hs, hr, rfl⟩
    have hle : ∀ k, s k ≤ M := by
      intro k
      by_cases hk : k ∈ s.support
      · have hk1 := hs k hk
        have h1 : s k ≤ rdeg ε s k.1 := by
          unfold rdeg
          have : k = (k.1, k.2.1, !ε k.1) := by
            obtain ⟨a, i, b⟩ := k
            simp only [inF1] at hk1
            simp [hk1]
          rw [this]
          exact Finset.single_le_sum (f := fun i => s (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h2 : rdeg ε s k.1 ≤ ∑ a, rdeg ε s a :=
          Finset.single_le_sum (f := fun a => rdeg ε s a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h3 : (∑ a, rdeg ε s a) ≤ M := Finset.le_sup (f := fun r : Fin m → ℕ => ∑ a, r a) (Finset.mem_coe.mp hr)
        omega
      · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _
    refine ⟨fun k => ⟨s k, Nat.lt_succ_of_le (hle k)⟩, Set.mem_univ _, ?_⟩
    congr 1
    ext k
    simp
  exact FiniteDimensional.span_of_finite ℂ hfin

theorem rdeg_filter (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) :
    rdeg ε (s.filter (inF1 ε)) = rdeg ε s := by
  funext a
  unfold rdeg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.filter_apply_pos]
  simp [inF1]

theorem monomial_split (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) (a : ℂ) :
    (monomial s a : PX m n) = monomial (s.filter (inF1 ε)) 1 * monomial (s.filter fun k => ¬ inF1 ε k) a ∧
      (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ box ε {rdeg ε s} ∧
      (monomial (s.filter fun k => ¬ inF1 ε k) a : PX m n) ∈ F2 ε := by
  refine ⟨by rw [monomial_mul, Finsupp.filter_pos_add_filter_neg, one_mul], ?_, ?_⟩
  · refine Submodule.subset_span ⟨s.filter (inF1 ε), fun k hk => ?_, by simp [rdeg_filter], rfl⟩
    rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
  · refine monomial_mem_supported' _ (fun k hk => ?_) a
    rw [Finsupp.support_filter, Finset.mem_filter] at hk
    exact hk.2

end PositivityTheory.Rg.Sw.LC.Core
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SumPderivXMem
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem fun_mem (ε : Fin m → Bool) (f : PX m n → PX m n) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) = x * f y + y * f x) (hC : ∀ r : ℂ, f (algebraMap ℂ (PX m n) r) = 0)
    (hgen : ∀ i j, f (Qp ε i j) ∈ QA ε) : ∀ R ∈ QA ε, f R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨i, j⟩, rfl⟩ := hx; exact hgen i j
  | algebraMap r => rw [hC]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd]; exact add_mem hx hy
  | mul x y hx' hy' hx hy => rw [hmul]; exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)

def dPhi (c : ℝ) (k : Fin m × Fin n × Bool) (P : PX m n) : PX m n := pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P

theorem mom_mul_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (U P : PX m n) :
    mom c (U * dPhi c k P) = -mom c (pderiv k U * P) := by
  have h := mom_dPhi c hc k (U * P)
  have e : U * dPhi c k P =
      (pderiv k (U * P) - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * (U * P)) - pderiv k U * P := by
    unfold dPhi
    rw [(pderiv k).leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, mom_sub c hc, h, zero_sub]

theorem pderiv_X_mem (ε : Fin m → Bool) (k l : Fin m × Fin n × Bool) : (pderiv k (X l : PX m n)) ∈ QA ε := by
  rw [pderiv_X, Pi.single_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

def fE (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, j, false) * pderiv (a, i, false) R

def fA (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, i, true) * pderiv (a, j, true) R

private theorem sum_X_mul_pderiv_mem_QA_of_generators (ε : Fin m → Bool) (g h : Fin m → Fin m × Fin n × Bool)
    (hgen : ∀ k l, (∑ a, X (g a) * pderiv (h a) (Qp ε k l) : PX m n) ∈ QA ε) :
    ∀ R ∈ QA ε, (∑ a, X (g a) * pderiv (h a) R : PX m n) ∈ QA ε := by
  apply fun_mem ε (fun R => ∑ a, X (g a) * pderiv (h a) R)
  · intro x y
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
  · intro x y
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun a _ => by ring)
  · intro r
    simp [Derivation.map_algebraMap]
  · exact hgen

theorem fE_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fE i j R ∈ QA ε := by
  intro R hR
  unfold fE
  refine sum_X_mul_pderiv_mem_QA_of_generators ε (fun a => (a, j, false)) (fun a => (a, i, false)) (fun k l => ?_) R hR
  simp only [pd_Qp_f]
  by_cases h : l = i
  · subst h
    have e : (∑ a, X (a, j, false) * (C (sgn ε a) * X (a, k, true)) : PX m n) = Qp ε k j := by
      rw [Qp_eq]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    simp only [if_true]
    rw [e]
    exact Qp_mem ε k j
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    exact zero_mem _

theorem fA_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fA i j R ∈ QA ε := by
  intro R hR
  unfold fA
  refine sum_X_mul_pderiv_mem_QA_of_generators ε (fun a => (a, i, true)) (fun a => (a, j, true)) (fun k l => ?_) R hR
  simp only [partial_deriv_quadratic_pairing]
  by_cases h : k = j
  · subst h
    have e : (∑ a, X (a, i, true) * (C (sgn ε a) * X (a, l, false)) : PX m n) = Qp ε i l := by
      rw [Qp_eq]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    simp only [if_true]
    rw [e]
    exact Qp_mem ε i l
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    exact zero_mem _

def Bf (ε : Fin m → Bool) (i j : Fin n) (U V : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, j, true) U * pderiv (a, i, false) V + pderiv (a, i, false) U * pderiv (a, j, true) V)

theorem Bf_comm (ε : Fin m → Bool) (i j : Fin n) (U V : PX m n) : Bf ε i j U V = Bf ε i j V U := by
  unfold Bf; exact Finset.sum_congr rfl fun _ _ => by ring

theorem Bf_der (ε : Fin m → Bool) (i j : Fin n) (U : PX m n) (hU : ∀ k l, Bf ε i j U (Qp ε k l) ∈ QA ε) :
    ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε :=
  fun_mem ε _ (fun x y => by simp only [Bf, map_add (f := _), mul_add, ← Finset.sum_add_distrib];
                             exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y => by simp only [Bf, Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib];
                   exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun r => by simp [Bf]) hU

theorem sgn3 (ε : Fin m → Bool) (a : Fin m) :
    (C (sgn ε a) : PX m n) * (C (sgn ε a) * C (sgn ε a)) = C (sgn ε a) := by
  rw [← map_mul, sgn_mul_self, map_one, mul_one]

theorem sumT (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, l, false) else 0) *
      (if q then C (sgn ε a) * X (a, k, true) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, and_self, and_true, and_false,
    true_and, false_and, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [Qp_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  linear_combination (X (a, k, true) * X (a, l, false) : PX m n) * sgn3 ε a

theorem sumT' (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, k, true) else 0) *
      (if q then C (sgn ε a) * X (a, l, false) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, and_self, and_true, and_false,
    true_and, false_and, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [Qp_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  linear_combination (X (a, k, true) * X (a, l, false) : PX m n) * sgn3 ε a

theorem ite_mem (ε : Fin m → Bool) (p : Prop) [Decidable p] (k l : Fin n) :
    (if p then (Qp ε k l : PX m n) else 0) ∈ QA ε := by
  split_ifs
  · exact Qp_mem ε k l
  · exact zero_mem _

theorem Bf_gen (ε : Fin m → Bool) (i j k l k' l' : Fin n) :
    Bf ε i j (Qp ε k l) (Qp ε k' l') ∈ QA ε := by
  simp only [Bf, pd_Qp_f, partial_deriv_quadratic_pairing, mul_add, Finset.sum_add_distrib, sumT, sumT']
  exact add_mem (ite_mem _ _ _ _) (ite_mem _ _ _ _)

theorem Bf_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ U ∈ QA ε, ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε := by
  intro U hU
  apply Bf_der ε i j U
  intro k l
  rw [Bf_comm]
  exact Bf_der ε i j (Qp ε k l) (fun k' l' => Bf_gen ε i j k l k' l') U hU

def fL (ε : Fin m → Bool) (i j : Fin n) (R : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * pderiv (a, j, true) (pderiv (a, i, false) R)

theorem fL_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fL ε i j R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, l⟩, rfl⟩ := hx
    have : fL ε i j (Qp ε k l : PX m n) =
        ∑ a, C (sgn ε a) * pderiv (a, j, true) (if l = i then C (sgn ε a) * X (a, k, true) else 0) := by
      simp only [fL, pd_Qp_f]
    rw [this]
    refine sum_mem fun a _ => mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) ?_
    split_ifs
    · rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
      exact mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) (pderiv_X_mem ε _ _)
    · simp
  | algebraMap r => simp [fL]
  | add x y _ _ hx hy => simpa [fL, mul_add, Finset.sum_add_distrib] using add_mem hx hy
  | mul x y hx' hy' hx hy =>
    have e : fL ε i j (x * y) = x * fL ε i j y + y * fL ε i j x + Bf ε i j x y := by
      simp only [fL, Bf, Derivation.leibniz, smul_eq_mul, map_add (f := _), Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact add_mem (add_mem (mul_mem hx' hy) (mul_mem hy' hx)) (Bf_mem ε i j x hx' y hy')

theorem sum_pderiv_X_mem (ε : Fin m → Bool) (R : PX m n) (hR : R ∈ QA ε) (f : Fin m → Fin m × Fin n × Bool)
    (g : Fin m → Fin m × Fin n × Bool) : (∑ a, R * pderiv (f a) (X (g a) : PX m n)) ∈ QA ε := by
  apply Subalgebra.sum_mem
  intro a _
  exact mul_mem hR (pderiv_X_mem ε _ _)

theorem nullStable : NullStable := by
  intro m n ε c hc i j P hP
  have hP' : ∀ R ∈ QA ε, mom c (R * P) = 0 := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    have e : R * lapS ε c i j P =
        ∑ a, (C (sgn ε a) * R) * dPhi c (a, i, false) (dPhi c (a, j, true) P) := by
      simp only [lapS, dPhi, Finset.mul_sum, Bool.not_false, Bool.not_true]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, pderiv_C_mul, neg_neg]
    rw [← mom_sum c hc]
    have e3 : (∑ a, C (sgn ε a) * pderiv (a, j, true) (pderiv (a, i, false) R) * P) =
        fL ε i j R * P := by
      simp only [fL, Finset.sum_mul]
    rw [e3]
    exact hP' _ (fL_mem ε i j R hR)
  · intro R hR
    have e : R * eulH c i j P = ∑ a, (R * X (a, j, false)) * dPhi c (a, i, false) P := by
      simp only [eulH, dPhi, Finset.mul_sum, Bool.not_false]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, Derivation.leibniz, smul_eq_mul]
    rw [Finset.sum_neg_distrib, ← mom_sum c hc]
    have e3 : (∑ a, (R * pderiv (a, i, false) (X (a, j, false)) + X (a, j, false) * pderiv (a, i, false) R) * P) =
        ((∑ a, R * pderiv (a, i, false) (X (a, j, false) : PX m n)) + fE i j R) * P := by
      simp only [fE, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hS : ((∑ a, R * pderiv (a, i, false) (X (a, j, false) : PX m n)) + fE i j R) ∈ QA ε :=
      add_mem (sum_pderiv_X_mem ε R hR (fun a => (a, i, false)) (fun a => (a, j, false)))
        (fE_mem ε i j R hR)
    rw [e3, hP' _ hS, neg_zero]
  · intro R hR
    have e : R * eulA c i j P = ∑ a, (R * X (a, i, true)) * dPhi c (a, j, true) P := by
      simp only [eulA, dPhi, Finset.mul_sum, Bool.not_true]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, Derivation.leibniz, smul_eq_mul]
    rw [Finset.sum_neg_distrib, ← mom_sum c hc]
    have e3 : (∑ a, (R * pderiv (a, j, true) (X (a, i, true)) + X (a, i, true) * pderiv (a, j, true) R) * P) =
        ((∑ a, R * pderiv (a, j, true) (X (a, i, true) : PX m n)) + fA i j R) * P := by
      simp only [fA, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hS : ((∑ a, R * pderiv (a, j, true) (X (a, i, true) : PX m n)) + fA i j R) ∈ QA ε :=
      add_mem (sum_pderiv_X_mem ε R hR (fun a => (a, j, true)) (fun a => (a, i, true)))
        (fA_mem ε i j R hR)
    rw [e3, hP' _ hS, neg_zero]
  · intro R hR
    simp only [mulQ, ← mul_assoc]
    exact hP' _ (mul_mem hR (Qp_mem ε i j))

end PositivityTheory.Rg.Sw.LC.NullS
end
end

