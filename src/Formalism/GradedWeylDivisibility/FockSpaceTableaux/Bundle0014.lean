module

public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0008

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
section
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma fockQ_eq_sum_coeff_mul_factorial_of_support_subset {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by
    by_contra hne
    exact hm (MvPolynomial.mem_support_iff.mpr hne)
  rw [h0]
  ring

private lemma fockQ_comm' {σ : Type*} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fockQ_eq_sum_coeff_mul_factorial_of_support_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

private lemma fockQ_finset_sum_right {σ ι : Type*} (f : MvPolynomial σ ℚ) (s : Finset ι)
    (G : ι → MvPolynomial σ ℚ) : fockQ f (∑ i ∈ s, G i) = ∑ i ∈ s, fockQ f (G i) := by
  unfold fockQ
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private lemma fockQ_add_right' {σ : Type*} (f g₁ g₂ : MvPolynomial σ ℚ) :
    fockQ f (g₁ + g₂) = fockQ f g₁ + fockQ f g₂ := by
  unfold fockQ
  simp only [MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib]

private lemma fockQ_add_left {σ : Type*} (f₁ f₂ g : MvPolynomial σ ℚ) :
    fockQ (f₁ + f₂) g = fockQ f₁ g + fockQ f₂ g := by
  rw [fockQ_comm', fockQ_add_right', fockQ_comm' g, fockQ_comm' g]

private lemma fockQ_C_mul_right {σ : Type*} (f g : MvPolynomial σ ℚ) (a : ℚ) :
    fockQ f (C a * g) = a * fockQ f g := by
  unfold fockQ
  simp only [MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private lemma fockQ_monomial_monomial {σ : Type*} [DecidableEq σ] (s t : σ →₀ ℕ) (a b : ℚ) :
    fockQ (monomial s a) (monomial t b) =
      if s = t then a * b * ((∏ k ∈ s.support, (s k).factorial : ℕ) : ℚ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst ha
    simp [fockQ]
  · rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset _ _ {s} (by rw [MvPolynomial.support_monomial, if_neg ha]),
      Finset.sum_singleton, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg (Ne.symm hst), if_neg hst]
      ring

private lemma nonneg_of_le_add_self {σ : Type*} [DecidableEq σ] (s : σ →₀ ℕ) (v : σ) :
    (∏ k ∈ (Finsupp.single v 1 + s : σ →₀ ℕ).support, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial) =
      (s v + 1) * ∏ k ∈ s.support, (s k).factorial := by
  have key : ∀ (m : σ →₀ ℕ) (S : Finset σ), m.support ⊆ S →
      ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ S, (m k).factorial := by
    intro m S hS
    apply Finset.prod_subset hS
    intro k _ hk
    have h0 : m k = 0 := by
      by_contra hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    rw [h0, Nat.factorial_zero]
  have h1 : (Finsupp.single v 1 + s : σ →₀ ℕ).support ⊆ insert v s.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right
      simpa [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hkv] using hk
  have h2 : s.support ⊆ insert v s.support := Finset.subset_insert _ _
  rw [key _ _ h1, key s _ h2]
  have hv : v ∈ insert v s.support := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ (fun k => (s k).factorial) hv]
  have h3 : ∏ k ∈ (insert v s.support).erase v, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v s.support).erase v, (s k).factorial := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.single_apply, Ne.symm hkv]
  rw [h3, Finsupp.add_apply, Finsupp.single_eq_same, add_comm 1 (s v), Nat.factorial_succ]
  try ring

private lemma fockQ_X_mul_monomial_eq_pderiv_monomial {σ : Type*} [DecidableEq σ] (v : σ) (s t : σ →₀ ℕ) (a b : ℚ) :
    fockQ (X v * monomial s a) (monomial t b) = fockQ (monomial s a) (pderiv v (monomial t b)) := by
  rw [X, monomial_mul, one_mul, pderiv_monomial, fockQ_monomial_monomial, fockQ_monomial_monomial]
  by_cases h : Finsupp.single v 1 + s = t
  · subst h
    have hs : Finsupp.single v 1 + s - Finsupp.single v 1 = s := add_tsub_cancel_left _ _
    rw [if_pos rfl, if_pos hs.symm, nonneg_of_le_add_self, Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  · rw [if_neg h]
    by_cases h' : s = t - Finsupp.single v 1
    · rw [if_pos h']
      have htv : t v = 0 := by
        by_contra hne
        apply h
        rw [h', add_comm]
        exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))
      rw [htv]
      simp
    · rw [if_neg h']

private lemma fockQ_X_mul_left_eq_pderiv_right {σ : Type*} [DecidableEq σ] (v : σ) (P Q : MvPolynomial σ ℚ) :
    fockQ (X v * P) Q = fockQ P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    induction Q using MvPolynomial.induction_on' with
    | monomial t b => exact fockQ_X_mul_monomial_eq_pderiv_monomial v s t a b
    | add q₁ q₂ h₁ h₂ => rw [map_add (f := _), fockQ_add_right', fockQ_add_right', h₁, h₂]
  | add p₁ p₂ h₁ h₂ => rw [mul_add, fockQ_add_left, fockQ_add_left, h₁, h₂]

private lemma fockQ_C_left_eq_mul_coeff_zero {σ : Type*} (a : ℚ) (Q : MvPolynomial σ ℚ) :
    fockQ (C a) Q = a * Q.coeff 0 := by
  classical
  rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset _ _ {0} (by
    rw [MvPolynomial.C_apply, MvPolynomial.support_monomial]
    split_ifs <;> simp), Finset.sum_singleton]
  simp [MvPolynomial.coeff_C]

private lemma rowAct_X_eq_sum_C_mul_X {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (v : Fin r × Fin n) :
    rowAct ℚ h (X v) = ∑ b : Fin r, C (h v.1 b) * X (b, v.2) := by
  simp [rowAct]

private lemma coeff_zero_rowAct_eq {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (Q : MvPolynomial (Fin r × Fin n) ℚ) :
    (rowAct ℚ h Q).coeff 0 = Q.coeff 0 := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    have hx : constantCoeff (rowAct ℚ h (X v)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [rowAct_X_eq_sum_C_mul_X, map_sum]
      simp
    change constantCoeff (rowAct ℚ h (p * X v)) = constantCoeff (p * X v)
    rw [map_mul, map_mul, hx, map_mul, MvPolynomial.constantCoeff_X, mul_zero, mul_zero]


set_option maxHeartbeats 800000 in
private lemma pderiv_rowAct_eq_sum_C_mul_rowAct_pderiv {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (w : Fin r × Fin n)
    (Q : MvPolynomial (Fin r × Fin n) ℚ) :
    pderiv w (rowAct ℚ h Q) = ∑ c : Fin r, C (h c w.1) * rowAct ℚ h (pderiv (c, w.2) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e1 : pderiv w (rowAct ℚ h (X v)) = if v.2 = w.2 then C (h v.1 w.1) else 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [rowAct_X_eq_sum_C_mul_X, map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply]
      by_cases hv : v.2 = w.2
      · rw [if_pos hv, Finset.sum_eq_single w.1]
        · simp [Prod.ext_iff, hv]
        · intro c _ hc
          rw [if_neg (fun hh : (c, v.2) = w => hc (by rw [← hh])), mul_zero]
        · simp
      · rw [if_neg hv]
        apply Finset.sum_eq_zero
        intro c _
        rw [if_neg (fun hh : (c, v.2) = w => hv (by rw [← hh])), mul_zero]
    have e3 : ∑ c : Fin r, C (h c w.1) * (if v = (c, w.2) then (1 : MvPolynomial (Fin r × Fin n) ℚ) else 0) =
        if v.2 = w.2 then C (h v.1 w.1) else 0 := by
      by_cases hv : v.2 = w.2
      · rw [if_pos hv, Finset.sum_eq_single v.1]
        · rw [if_pos (show v = (v.1, w.2) from Prod.ext rfl hv), mul_one]
        · intro c _ hc
          rw [if_neg (fun hh : v = (c, w.2) => hc (by rw [hh])), mul_zero]
        · simp
      · rw [if_neg hv]
        apply Finset.sum_eq_zero
        intro c _
        rw [if_neg (fun hh : v = (c, w.2) => hv (by rw [hh])), mul_zero]
    have e4 : ∀ c : Fin r, rowAct ℚ h (pderiv (c, w.2) (p * X v)) =
        rowAct ℚ h p * (if v = (c, w.2) then 1 else 0) + rowAct ℚ h (X v) * rowAct ℚ h (pderiv (c, w.2) p) := by
      intro c
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply, map_add (f := _), map_mul, map_mul]
      split_ifs <;> simp
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp, e1]
    simp_rw [e4]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← e3, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun c _ => by ring)) (Finset.sum_congr rfl (fun c _ => by ring))

theorem fock_space_row_action : FockQRowAct := by
  intro r n g P Q
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a =>
    have hC : rowAct ℚ g (C a : MvPolynomial (Fin r × Fin n) ℚ) = C a := by simp [rowAct]
    rw [hC, fockQ_C_left_eq_mul_coeff_zero, fockQ_C_left_eq_mul_coeff_zero, coeff_zero_rowAct_eq]
  | add p q hp hq => rw [map_add (f := _), fockQ_add_left, fockQ_add_left, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, rowAct_X_eq_sum_C_mul_X]
    have e5 : rowAct ℚ g p * ∑ b : Fin r, C (g v.1 b) * X (b, v.2) =
        ∑ b : Fin r, C (g v.1 b) * (X (b, v.2) * rowAct ℚ g p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e5, fockQ_comm', fockQ_finset_sum_right]
    have e6 : ∀ b : Fin r, fockQ Q (C (g v.1 b) * (X (b, v.2) * rowAct ℚ g p)) =
        g v.1 b * fockQ p (rowAct ℚ g.transpose (pderiv (b, v.2) Q)) := by
      intro b
      rw [fockQ_C_mul_right, fockQ_comm', fockQ_X_mul_left_eq_pderiv_right, hp]
    rw [Finset.sum_congr rfl (fun b _ => e6 b), mul_comm p (X v), fockQ_X_mul_left_eq_pderiv_right, pderiv_rowAct_eq_sum_C_mul_rowAct_pderiv, fockQ_finset_sum_right]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [fockQ_C_mul_right, Matrix.transpose_apply]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQWordAdj
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

lemma leadj_applyWord_cons {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := by
  rfl

lemma leadj_applyWord_append {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (l1 ++ l2) F = applyWord ℚ l1 (applyWord ℚ l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

lemma leadj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

theorem fock_space_word_adjoint : FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; simp [applyWord, transposeWord]
  | cons x w ih =>
    intro F G
    rw [leadj_applyWord_cons, fockQRowDivAdj, ih, leadj_transposeWord_cons, leadj_applyWord_append]
    simp [applyWord]

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lehw_dom {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℚ) (hf : f ∈ dualWeyl ℚ r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  intro m hm k
  let N : ℕ := ∏ d ∈ f.support, (AddMonoidAlgebra.coeff f d).den
  let u : MvPolynomial (Fin r × Fin n) ℤ := ∑ d ∈ f.support,
    monomial d ((∏ d' ∈ f.support.erase d, ((AddMonoidAlgebra.coeff f d').den : ℤ)) * (AddMonoidAlgebra.coeff f d).num)
  have hu : map (Int.castRingHom ℚ) u = (N : ℚ) • f := by
    conv_rhs => rw [f.as_sum]
    rw [Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, map_sum, map_monomial, smul_monomial]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    push_cast
    have hN : (N : ℚ) = (∏ d' ∈ f.support.erase d, ((AddMonoidAlgebra.coeff f d').den : ℚ)) * (AddMonoidAlgebra.coeff f d).den := by
      simp only [N]
      push_cast
      rw [Finset.prod_erase_mul _ _ hd]
    rw [smul_eq_mul, hN, mul_assoc, Rat.den_mul_eq_num]
    simp [eq_intCast]
  have hN0 : (N : ℚ) ≠ 0 := by
    simp only [N]
    push_cast
    exact Finset.prod_ne_zero_iff.mpr fun d _ => Nat.cast_ne_zero.mpr (AddMonoidAlgebra.coeff f d).den_nz
  have huD : u ∈ dualWeyl ℤ r n ν :=
    (dualWeylIntRat r n ν u).mpr (by rw [hu]; exact (dualWeyl ℚ r n ν).smul_mem _ hf)
  have hmu : m ∈ u.support := by
    rw [mem_support_iff]
    intro h0
    have e := congrArg (AddMonoidAlgebra.coeff · m) hu
    rw [coeff_map, h0, map_zero, coeff_smul, smul_eq_mul] at e
    exact (mem_support_iff.mp hm) ((mul_eq_zero.mp e.symm).resolve_left hN0)
  exact (dualWeylDominanceZ r n ν hnr hν u huD m hmu).1 k

def LehwShift {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ)
    (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous w (P.coeff k) (μ + k * δ)

theorem lehwShift_mul {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LehwShift w P μ δ) (hQ : LehwShift w Q μ' δ) : LehwShift w (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (hP x.1).mul (hQ x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

theorem lehwShift_one {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ) :
    LehwShift w (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [Polynomial.coeff_one_zero]
    intro d hd
    rw [MvPolynomial.coeff_one] at hd
    split_ifs at hd with h
    · subst h
      simp
    · exact (hd rfl).elim
  · rw [Polynomial.coeff_one, if_neg (by omega)]
    intro d hd
    exact (hd (by simp)).elim

theorem lehwShift_pow {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LehwShift w P μ δ) (e : ℕ) : LehwShift w (P ^ e) (e • μ) δ := by
  induction e with
  | zero => simpa using lehwShift_one (R := R) w δ
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact lehwShift_mul ih hP

theorem lehwShift_prod {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ} {ι : Type*}
    (s : Finset ι) (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LehwShift w (P i) (μ i) δ) : LehwShift w (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using lehwShift_one (R := R) w δ
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lehwShift_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lehwShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (c : R) (δ : ℤ) :
    LehwShift w (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  have h1 := lehwShift_one (R := R) w δ k
  rw [Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1))

theorem lehwShift_gen {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (v : Fin r × Fin n) :
    LehwShift w (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (w v) δ := by
  obtain ⟨c, s⟩ := v
  intro k
  by_cases hc : c = b
  · subst hc
    rw [if_pos (show (c, s).1 = c from rfl)]
    rcases k with _ | _ | k
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (c, s) := by simp
      rw [e]
      simpa using isWeightedHomogeneous_X R w (c, s)
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (0 + 1) = X (a, s) := by simp
      rw [e]
      convert isWeightedHomogeneous_X R w (a, s) using 1
      rw [hstep s]
      push_cast
      ring
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (k + 1 + 1) = 0 := by
        simp [Polynomial.coeff_C]
      rw [e]
      intro d hd
      exact (hd (by simp)).elim
  · rw [if_neg (show ¬ (c, s).1 = b from hc), add_zero, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk
      simpa using isWeightedHomogeneous_X R w (c, s)
    · intro d hd
      exact (hd (by simp)).elim

theorem lehwShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LehwShift w (rowGen R a b (monomial d c)) (Finsupp.weight w d) δ := by
  unfold rowGen
  rw [MvPolynomial.aeval_monomial, Finsupp.weight_apply]
  have h := lehwShift_mul (lehwShift_algebraMap (R := R) w c δ)
    (lehwShift_prod d.support _ (fun v => d v • w v) δ
      (fun v _ => lehwShift_pow (lehwShift_gen (R := R) w δ a b hstep v) (d v)))
  simpa [Finsupp.prod, Finsupp.sum] using h

theorem lehw_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (H : ℤ) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous w f H) :
    IsWeightedHomogeneous w (rowDiv R a b k f) (H + k * δ) := by
  unfold rowDiv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, Polynomial.finsetSum_coeff]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun d hd => ?_)
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := lehwShift_rowGen_monomial R w δ a b hstep d (AddMonoidAlgebra.coeff f d) k
  rw [hf (mem_support_iff.mp hd)] at h
  exact h

def lehwP {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℤ := fun v => if v.1.val ≤ a.val then 1 else 0

theorem highestWeightCount_self_eq_succ_of_lt {r n : ℕ} {a b : Fin r} (hab : a < b) (s : Fin n) :
    lehwP (n := n) a (a, s) = lehwP a (b, s) + 1 := by
  have h : a.val < b.val := hab
  simp [lehwP, show ¬ b.val ≤ a.val by omega]

theorem lehw_weight_P {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lehwP a) m = ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [rowDeg, lehwP]
  by_cases h : a'.val ≤ a.val
  · simp [h, show a'.val < a.val + 1 by omega]
  · simp [h, show ¬ a'.val < a.val + 1 by omega]

theorem lehw_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp [rowDeg]
  · intro b _ hb
    simp [hb, Ne.symm hb]
  · simp

theorem lehw_kill {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) ℚ) (hG : G ∈ dualWeyl ℚ r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℚ a b k G = 0 := by
  have hH := rowDivStable ℚ r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hGP : IsWeightedHomogeneous (lehwP (n := n) a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro d hd
    rw [lehw_weight_P]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hGh hd]
  have hshift := lehw_rowDiv_shift ℚ (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGP
  have hmw := hshift hm
  rw [lehw_weight_P] at hmw
  have hdom := lehw_dom ν hn hν _ hH m (mem_support_iff.mpr hm) (a.val + 1)
  omega

end Formalism.GradedWeylDivisibility
end
end

