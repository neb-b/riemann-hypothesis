module

public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
public import Formalism.GradedWeylDivisibility.StatementA

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma lfockq_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset h (fun m _ hm => ?_)
  have hz : f.coeff m = 0 := by
    by_contra hne
    exact hm (MvPolynomial.mem_support_iff.mpr hne)
  simp [hz]

lemma lfockq_symm (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [lfockq_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    lfockq_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

lemma lfockq_self_pos (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockQ f f := by
  unfold fockQ
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hf (MvPolynomial.support_eq_empty.mp he)
  refine Finset.sum_pos (fun m hm => ?_) hne
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hw : (0 : ℚ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Finset.prod_pos (fun k _ => Nat.factorial_pos _))
  exact mul_pos (mul_self_pos.mpr hc) hw

lemma lfockq_add_left (f f' g : MvPolynomial σ ℚ) :
    fockQ (f + f') g = fockQ f g + fockQ f' g := by
  classical
  rw [lfockq_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    lfockq_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    lfockq_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

lemma lfockq_smul_left (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g := by
  rw [lfockq_eq_sum (c • f) g f.support MvPolynomial.support_smul,
    lfockq_eq_sum f g f.support subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

end general

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lgraded_wa {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℕ := fun v => if v.1 = a then 1 else 0

theorem lgraded_rowGen_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  obtain ⟨b, j⟩ := v
  simp only [rowGen, aeval_X, lgraded_wa]
  by_cases h : b = a
  · subst h
    rw [if_pos rfl, if_pos rfl, pow_one]
    ring
  · simp [h]

theorem lgraded_rowGen_C {r n : ℕ} (a : Fin r) (c : ℚ) :
    rowGen ℚ a a (C c : MvPolynomial (Fin r × Fin n) ℚ) = Polynomial.C (C c) := by
  rw [rowGen, aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem lgraded_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowGen ℚ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next => rw [monomial_zero', lgraded_rowGen_C]; simp
  next v k m _ _ ih =>
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v k) = k * lgraded_wa a v := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [add_comm, monomial_add_single, map_mul, ih, map_pow, lgraded_rowGen_X, map_add (f := _), map_mul,
      map_pow, hw, mul_pow, ← pow_mul, pow_add, mul_comm (lgraded_wa a v) k]
    ring

theorem lgraded_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowDiv ℚ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) • monomial m c := by
  rw [rowDiv, lgraded_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

theorem lgraded_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowDiv ℚ a a 1 f) m = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) * AddMonoidAlgebra.coeff f m := by
  induction f using MvPolynomial.induction_on'
  next m' c' =>
    rw [lgraded_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  next p q hp hq =>
    have hpq : rowDiv ℚ a a 1 (p + q) = rowDiv ℚ a a 1 p + rowDiv ℚ a a 1 q := by
      simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]
    rw [hpq, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem lgraded_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = Finsupp.weight (lgraded_wa a) m := by
  simp only [Finsupp.weight_apply, rowW, lgraded_wa]
  simp only [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : v.1 = a
  · simp [h]
  · simp [h, Ne.symm h]

private lemma exists_mem_coeff_eq_prod_weight_sub_mul_coeff {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : RowDivClosed M) (a : Fin r) (T : Finset ℕ) : ∀ g ∈ M, ∃ h ∈ M, ∀ m, AddMonoidAlgebra.coeff h m =
      (∏ s ∈ T, (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ))) * AddMonoidAlgebra.coeff g m := by
  classical
  induction T using Finset.induction_on
  next => intro g hg; exact ⟨g, hg, fun m => by simp⟩
  next s T hs ih =>
    intro g hg
    obtain ⟨h, hh, hc⟩ := ih g hg
    refine ⟨rowDiv ℚ a a 1 h - (s : ℚ) • h, M.sub_mem (hM a a 1 h hh) (M.smul_mem _ hh), fun m => ?_⟩
    rw [coeff_sub, coeff_smul, lgraded_coeff_euler, hc, Finset.prod_insert hs, smul_eq_mul]
    ring

theorem lgraded_sep {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  intro f hf hV t
  classical
  obtain ⟨h, hh, hc⟩ := exists_mem_coeff_eq_prod_weight_sub_mul_coeff M hM a (V.erase t) f hf
  have key : weightedHomogeneousComponent (lgraded_wa a) t f =
      (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ)))⁻¹ • h := by
    ext m
    rw [coeff_weightedHomogeneousComponent, coeff_smul, hc, smul_eq_mul]
    by_cases hm : m ∈ f.support
    · have hmV := hV m hm
      split_ifs with hw
      · rw [hw]
        have hne : (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ))) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro s hs
          have hst := (Finset.mem_erase.1 hs).1
          exact sub_ne_zero.2 (by exact_mod_cast hst.symm)
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      · have hmem : Finsupp.weight (lgraded_wa a) m ∈ V.erase t := Finset.mem_erase.2 ⟨hw, hmV⟩
        have h0 : ∏ s ∈ V.erase t,
            (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ)) = 0 :=
          Finset.prod_eq_zero hmem (sub_self _)
        rw [h0]
        simp
    · rw [mem_support_iff, not_not] at hm
      simp [hm]
  rw [key]
  exact M.smul_mem _ hh

theorem lgraded_multi {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, AddMonoidAlgebra.coeff h m =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then AddMonoidAlgebra.coeff f m else 0 := by
  classical
  induction A using Finset.induction_on
  next => intro f hf; exact ⟨f, hf, fun m => by simp⟩
  next b A hb ih =>
    intro f hf
    obtain ⟨h, hh, hc⟩ := ih f hf
    refine ⟨weightedHomogeneousComponent (lgraded_wa b) (μ b) h,
      lgraded_sep M hM b (h.support.image (Finsupp.weight (lgraded_wa b))) h hh
        (fun m hm => Finset.mem_image_of_mem _ hm) (μ b), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, hc]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : Finsupp.weight (lgraded_wa b) m = μ b <;> simp [h1]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lhwinHt (r n : ℕ) : Fin r × Fin n → ℤ := fun v => (v.1.val : ℤ)

def LhwinShift {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (lhwinHt r n) (P.coeff k) (μ + k * δ)

theorem lhwinShift_mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LhwinShift P μ δ) (hQ : LhwinShift Q μ' δ) : LhwinShift (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ) := by
    rw [← hx']; push_cast; ring
  rw [e]
  exact (hP x.1).mul (hQ x.2)

theorem lhwinShift_one {R : Type*} [CommRing R] {r n : ℕ} (δ : ℤ) :
    LhwinShift (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (lhwinHt r n)
  · exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LhwinShift P μ δ) (e : ℕ) : LhwinShift (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact lhwinShift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact lhwinShift_mul ih hP

theorem lhwinShift_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LhwinShift (P i) (μ i) δ) : LhwinShift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lhwinShift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact lhwinShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lhwinShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) (δ : ℤ) :
    LhwinShift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (lhwinHt r n) c
  · exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    LhwinShift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (lhwinHt r n v) ((a.val : ℤ) - b.val) := by
  intro k
  have hX : IsWeightedHomogeneous (lhwinHt r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (lhwinHt r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : lhwinHt r n v + ((1 : ℕ) : ℤ) * ((a.val : ℤ) - b.val) = lhwinHt r n (a, v.2) := by
          simp [lhwinHt, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LhwinShift (rowGen R a b (monomial d c)) (Finsupp.weight (lhwinHt r n) d)
      ((a.val : ℤ) - b.val) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine lhwinShift_mul (lhwinShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact lhwinShift_prod _ _ _ _ fun v _ => lhwinShift_pow (lhwinShift_gen a b v) _

theorem lhwin_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (lhwinHt r n) f H) :
    IsWeightedHomogeneous (lhwinHt r n) (rowDiv R a b k f) (H + k * ((a.val : ℤ) - b.val)) := by
  unfold rowDiv
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := lhwinShift_rowGen_monomial R a b d (AddMonoidAlgebra.coeff f d) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem lhwin_weight_ht {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lhwinHt r n) d =
      ∑ a : Fin r, (a.val : ℤ) * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, lhwinHt, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]

theorem lhwin_weight_nonneg {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight (lhwinHt r n) d := by
  rw [lhwin_weight_ht]
  exact Finset.sum_nonneg fun a _ => by positivity

theorem lhwin_nonneg {R : Type*} [CommRing R] {r n : ℕ} {g : MvPolynomial (Fin r × Fin n) R} {z : ℤ}
    (hg : g ≠ 0) (hz : IsWeightedHomogeneous (lhwinHt r n) g z) : 0 ≤ z := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hg
  rw [← hz hd]
  exact lhwin_weight_nonneg d

theorem lhwin_exists_killed (h2 : RowDivClosedGraded) {r n : ℕ}
    (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℚ a b k v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ IsWeightedHomogeneous (lhwinHt r n) v (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf0
    refine ⟨∑ a : Fin r, a.val * Finsupp.weight (rowW r n) d a,
      weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) d) f,
      h2 r n M hM f hfM _, ?_, ?_⟩
    · intro h
      apply hd
      have := congrArg (AddMonoidAlgebra.coeff · d) h
      simpa only [coeff_weightedHomogeneousComponent, if_pos rfl, if_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this
    · intro e he
      rw [coeff_weightedHomogeneousComponent] at he
      split_ifs at he with hμ
      · rw [lhwin_weight_ht, hμ]; push_cast; rfl
      · exact absurd rfl he
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab k hk => ?_⟩
  by_contra hne'
  have hH := lhwin_rowDiv_shift ℚ _ a b k v hvH
  have hnn := lhwin_nonneg hne' hH
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hlt : ((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b k v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadInterlaced
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclint_degreeOf_none_rename_some {B : Type*} [CommRing B] {σ : Type*}
    (p : MvPolynomial σ B) : degreeOf none (rename (some : σ → Option σ) p) = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)
  intro m hm
  rw [support_rename_of_injective (Option.some_injective σ)] at hm
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hm
  exact (Finsupp.mapDomain_of_notMem_range m' none (by simp)).le

private theorem colAddGen_eq_rename_some_of_mem_dualWeyl {B : Type*} [CommRing B] {r n : ℕ}
    {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) B} (hf : f ∈ dualWeyl B r n ν)
    {l j : Fin n} (hlj : l < j) :
    colAddGen B l j f = rename some f := by
  unfold dualWeyl at hf
  rw [Submodule.mem_inf] at hf
  have h := hf.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp (h l j hlj)

theorem leadInterlaced_of (h1 : CompDeg) (h2 : LeadComp) (h3 : TwoColumn) : LeadInterlaced := by
  intro B _ _ r n ν f hf hf0
  intro l j hlj
  have hlt : l < j := Fin.lt_def.mpr (by omega)
  have hdeg : (colLex r n).degree
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      (colLex r n).degree f :=
    h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f
  have hcoeff : AddMonoidAlgebra.coeff (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f)
      ((colLex r n).degree f) =
      AddMonoidAlgebra.coeff f ((colLex r n).degree f) := by
    simp only [coeff_weightedHomogeneousComponent, ↓reduceIte]
  have hg0 : weightedHomogeneousComponent (pairW (r := r) l j)
      (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by
    intro h
    have hne : AddMonoidAlgebra.coeff f ((colLex r n).degree f) ≠ 0 :=
      (colLex r n).coeff_degree_ne_zero_iff.mpr hf0
    apply hne
    rw [← hcoeff, h]
    rfl
  have hcol : degreeOf none (colAddGen B l j f) ≤ 0 := by
    rw [colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]
  have hcomp := h1 B r n l j
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol
  have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := pairW (r := r) l j)
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f
  have key := h3 B r n l j hlt 0 0
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom
    (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp
  rw [hdeg] at key
  exact key

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.StandardMonomialSpanOf
section
namespace Formalism.GradedWeylDivisibility

theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem applyWord_hw_mem_dualWeyl
    (h1 : HWMem) (h2 : RowDivStable)
    (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ w : List (Fin r × Fin r × ℕ),
      applyWord R w (hw R hn ν) ∈ dualWeyl R r n ν := fun
  | [] => h1 R r n hn ν hν
  | x :: w => h2 R r n ν x.1 x.2.1 x.2.2 _
      (applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w)

theorem weylLeDual_of (h1 : HWMem) (h2 : RowDivStable) : WeylLeDual := by
  intro R _ r n hn ν hν
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) =>
      applyWord R w (hw R hn ν)) ≤ dualWeyl R r n ν
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w

end Formalism.GradedWeylDivisibility
end
end

