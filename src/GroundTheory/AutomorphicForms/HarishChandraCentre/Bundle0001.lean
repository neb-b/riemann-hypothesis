module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.FischerForm
section
namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {σ : Type*}

def mfact (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

theorem mfact_pos (m : σ →₀ ℕ) : 0 < mfact m :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem mfact_add_single [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by
  unfold mfact
  have h1 := Finsupp.mul_prod_erase' (s + Finsupp.single a 1) a (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' s a (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase a (s + Finsupp.single a 1) = Finsupp.erase a s := by
    ext v
    by_cases hv : v = a
    · subst hv; simp
    · simp [Finsupp.erase_ne hv]
  rw [← h1, ← h2, he]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

noncomputable def fischer (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ g.support, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m

theorem fischer_eq_sum (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m :=
  Finset.sum_subset hg fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]

theorem fischer_add_left (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by
  simp only [fischer, MvPolynomial.coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem fischer_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by
  simp only [fischer, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fischer_add_right (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by
  classical
  set s := g.support ∪ g'.support
  rw [fischer_eq_sum f (g + g') s (MvPolynomial.support_add),
    fischer_eq_sum f g s Finset.subset_union_left, fischer_eq_sum f g' s Finset.subset_union_right]
  simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem fischer_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer f (c • g) = c * fischer f g := by
  rw [fischer_eq_sum f (c • g) g.support (MvPolynomial.support_smul), fischer, Finset.mul_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem fischer_zero_left (g : MvPolynomial σ ℂ) : fischer 0 g = 0 := by simp [fischer]

@[simp] theorem fischer_zero_right (f : MvPolynomial σ ℂ) : fischer f 0 = 0 := by simp [fischer]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fischer (∑ i ∈ s, f i) g = ∑ i ∈ s, fischer (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ)
    (g : ι → MvPolynomial σ ℂ) : fischer f (∑ i ∈ s, g i) = ∑ i ∈ s, fischer f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_conj_symm (f g : MvPolynomial σ ℂ) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum g f (f.support ∪ g.support) Finset.subset_union_left,
    fischer_eq_sum f g (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, Complex.conj_conj]
  ring

theorem fischer_monomial [DecidableEq σ] (s t : σ →₀ ℕ) (c d : ℂ) :
    fischer (monomial s c) (monomial t d) = if s = t then (mfact s : ℂ) * star c * d else 0 := by
  rw [fischer_eq_sum _ _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton]
  simp only [coeff_monomial]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

theorem fischer_X_mul (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, fischer_add_left, fischer_add_left, hp, hq]
  | monomial s c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [fischer_add_right, map_add (f := _), fischer_add_right, hp, hq]
    | monomial t d =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial, fischer_monomial]
      by_cases ht : t a = 0
      · have hne : Finsupp.single a 1 + s ≠ t := by
          intro h
          have := congrArg (fun m => m a) h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          omega
        rw [if_neg hne]
        split_ifs <;> simp [ht]
      · have hle : Finsupp.single a 1 ≤ t := by
          intro v
          by_cases hv : v = a
          · subst hv; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_apply, if_neg (Ne.symm hv)]; exact Nat.zero_le _
        have hiff : Finsupp.single a 1 + s = t ↔ s = t - Finsupp.single a 1 := by
          constructor
          · rintro rfl; simp
          · rintro rfl; rw [add_comm]; exact tsub_add_cancel_of_le hle
        by_cases h : s = t - Finsupp.single a 1
        · have h' := hiff.2 h
          rw [if_pos h', if_pos h]
          have hsa : (s a + 1 : ℕ) = t a := by
            rw [← h']; simp [add_comm]
          rw [add_comm (Finsupp.single a 1) s, mfact_add_single, ← hsa]
          push_cast
          ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem fischer_pderiv (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (pderiv a f) g = fischer f (X a * g) := by
  rw [← fischer_conj_symm, ← fischer_X_mul, fischer_conj_symm]

theorem fischer_self (f : MvPolynomial σ ℂ) :
    fischer f f = ((∑ m ∈ f.support, (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) : ℝ) : ℂ) := by
  rw [fischer]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem fischer_self_eq_zero_iff (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [fischer_self, Complex.ofReal_eq_zero] at h
  have hnn : ∀ m ∈ f.support, 0 ≤ (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) :=
    fun m _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext m
  by_contra hm
  have hm' : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have := hz m hm'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (Nat.cast_ne_zero.2 (mfact_pos m).ne') h1
  · exact hm (Complex.normSq_eq_zero.1 h1)

end GroundTheory.Automorphic.HarishChandra
end

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE
section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev gl (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev U (n : ℕ) := UniversalEnvelopingAlgebra ℂ (gl n)

variable {n : ℕ}

def E (a : Fin n × Fin n) : gl n := Matrix.single a.1 a.2 1

noncomputable def e (a : Fin n × Fin n) : U n := UniversalEnvelopingAlgebra.ι ℂ (E a)

noncomputable def word (w : List (Fin n × Fin n)) : U n := (w.map e).prod

@[simp] theorem word_nil : word ([] : List (Fin n × Fin n)) = 1 := rfl

@[simp] theorem word_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    word (a :: w) = e a * word w := by
  simp [word]

@[simp] theorem word_append (v w : List (Fin n × Fin n)) : word (v ++ w) = word v * word w := by
  simp [word]

theorem word_singleton (a : Fin n × Fin n) : word [a] = e a := by simp

theorem E_mul_sub_mul (a b : Fin n × Fin n) :
    E a * E b - E b * E a =
      (if a.2 = b.1 then E (a.1, b.2) else 0) - (if b.2 = a.1 then E (b.1, a.2) else 0) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨k, l⟩ := b
  simp only [E]
  congr 1
  · by_cases h : j = k
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]
  · by_cases h : l = i
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]

theorem e_mul_sub_mul (a b : Fin n × Fin n) :
    e a * e b - e b * e a =
      (if a.2 = b.1 then e (a.1, b.2) else 0) - (if b.2 = a.1 then e (b.1, a.2) else 0) := by
  have h := congrArg (UniversalEnvelopingAlgebra.ι ℂ (L := gl n)) (E_mul_sub_mul a b)
  rw [← LieRing.of_associative_ring_bracket, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    at h
  simp only [e] at h ⊢
  rw [h, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem eq_sum_E (X : gl n) : X = ∑ a : Fin n × Fin n, X a.1 a.2 • E a := by
  ext i j
  simp only [E, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem ι_eq_sum_e (X : gl n) :
    UniversalEnvelopingAlgebra.ι ℂ X = ∑ a : Fin n × Fin n, X a.1 a.2 • e (n := n) a := by
  conv_lhs => rw [eq_sum_E X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [e, map_sum, map_smul]

theorem U.induction {C : U n → Prop}
    (halg : ∀ r : ℂ, C (algebraMap ℂ _ r)) (hι : ∀ x, C (UniversalEnvelopingAlgebra.ι ℂ x))
    (hmul : ∀ a b, C a → C b → C (a * b)) (hadd : ∀ a b, C a → C b → C (a + b))
    (u : U n) : C u := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep u
  show C (UniversalEnvelopingAlgebra.mkAlgHom ℂ (gl n) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb

theorem mem_center_of_commute_e {z : U n} (hz : ∀ a, e a * z = z * e a) :
    z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  induction u using U.induction with
  | halg r => exact Algebra.commutes r z
  | hι X =>
    rw [ι_eq_sum_e, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, mul_smul_comm, hz]
  | hmul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]

end GroundTheory.Automorphic.HarishChandra
end

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.RepBase
section
namespace GroundTheory.Automorphic.HarishChandra

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

variable {n : ℕ}

noncomputable def rowOp (i j : Fin n) : Module.End ℂ (Poly n) :=
  ∑ k : Fin n, (LinearMap.mulLeft ℂ (MvPolynomial.X (i, k) : Poly n)) ∘ₗ
    (MvPolynomial.pderiv (j, k) : Derivation ℂ (Poly n) (Poly n)).toLinearMap

theorem rowOp_apply (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by
  simp [rowOp, LinearMap.sum_apply]

end GroundTheory.Automorphic.HarishChandra
end

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.Symmetric
section
namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial Finset

variable {n : ℕ}

noncomputable abbrev psumFin (k : Fin n) : MvPolynomial (Fin n) ℂ := psum (Fin n) ℂ ((k : ℕ) + 1)

theorem esymm_mem_adjoin_psum (k : ℕ) (hk : k ≤ n) :
    esymm (Fin n) ℂ k ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℂ (Set.range (psumFin (n := n)))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [esymm_zero]; exact A.one_mem
  have hps : ∀ j, 1 ≤ j → j ≤ n → psum (Fin n) ℂ j ∈ A := by
    intro j hj1 hjn
    refine Algebra.subset_adjoin ⟨⟨j - 1, by omega⟩, ?_⟩
    show psum (Fin n) ℂ (j - 1 + 1) = psum (Fin n) ℂ j
    rw [Nat.sub_add_cancel hj1]
  have hsum : (k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k ∈ A := by
    rw [mul_esymm_eq_sum]
    refine A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (A.sum_mem fun a ha => ?_)
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    exact A.mul_mem (A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (ih a.1 ha.2 (by omega)))
      (hps a.2 (by omega) (by omega))
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have e : esymm (Fin n) ℂ k =
      (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ) k, smul_eq_C_mul, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hk', C_1, one_mul]
  rw [e]
  exact A.smul_mem hsum _

theorem aeval_mem_of_forall_mem {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, f i ∈ A) (F : MvPolynomial (Fin n) ℂ) :
    aeval f F ∈ A := by
  induction F using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact A.algebraMap_mem r
  | add p q hp hq => rw [map_add (f := _)]; exact A.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact A.mul_mem hp (hf i)

theorem mem_adjoin_psum_of_isSymmetric {p : MvPolynomial (Fin n) ℂ} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  obtain ⟨F, hF⟩ := esymmAlgHom_fin_surjective ℂ (le_refl n) ⟨p, hp⟩
  have e := congrArg Subtype.val hF
  rw [esymmAlgHom_apply] at e
  have e' : aeval (fun i : Fin n => esymm (Fin n) ℂ ((i : ℕ) + 1)) F = p := e
  rw [← e']
  exact aeval_mem_of_forall_mem _ (fun i => esymm_mem_adjoin_psum _ (by omega)) F

def TopClose (k : ℕ) (a b : MvPolynomial (Fin n) ℂ) : Prop :=
  a.totalDegree ≤ k ∧ b.totalDegree ≤ k ∧ (a = b ∨ (a - b).totalDegree < k)

theorem TopClose.one : TopClose (n := n) 0 1 1 := by
  refine ⟨by simp, by simp, Or.inl rfl⟩

theorem TopClose.mul {k l : ℕ} {a b a' b' : MvPolynomial (Fin n) ℂ} (h : TopClose k a b)
    (h' : TopClose l a' b') : TopClose (k + l) (a * a') (b * b') := by
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨ha', hb', hab'⟩ := h'
  refine ⟨(totalDegree_mul _ _).trans (add_le_add ha ha'),
    (totalDegree_mul _ _).trans (add_le_add hb hb'), ?_⟩
  by_cases e : a = b ∧ a' = b'
  · left; rw [e.1, e.2]
  right
  have key : a * a' - b * b' = (a - b) * a' + b * (a' - b') := by ring
  rw [key]
  refine lt_of_le_of_lt (totalDegree_add _ _) (max_lt ?_ ?_)
  · rcases hab with h1 | h1
    · rw [h1, sub_self, zero_mul, totalDegree_zero]
      rcases hab' with h2 | h2
      · exact absurd ⟨h1, h2⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)
  · rcases hab' with h1 | h1
    · rw [h1, sub_self, mul_zero, totalDegree_zero]
      rcases hab with h2 | h2
      · exact absurd ⟨h2, h1⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)

theorem TopClose.pow {k : ℕ} {a b : MvPolynomial (Fin n) ℂ} (h : TopClose k a b) (c : ℕ) :
    TopClose (c * k) (a ^ c) (b ^ c) := by
  induction c with
  | zero => simpa using TopClose.one
  | succ c ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact ih.mul h

theorem TopClose.prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a b : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ i ∈ s, TopClose (k i) (a i) (b i)) :
    TopClose (∑ i ∈ s, k i) (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopClose.one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

theorem isHomogeneous_psum (k : ℕ) : (psum (Fin n) ℂ k).IsHomogeneous k := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k

def psumWt (c : Fin n →₀ ℕ) : ℕ := ∑ i ∈ c.support, c i * ((i : ℕ) + 1)

theorem symmetric_le_adjoin (q : Fin n → MvPolynomial (Fin n) ℂ) (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) (d : ℕ) :
    ∀ p : MvPolynomial (Fin n) ℂ, p.IsSymmetric → p.totalDegree ≤ d →
      p ∈ Algebra.adjoin ℂ (Set.range q) := by
  set B := Algebra.adjoin ℂ (Set.range q)
  have hBsym : ∀ r ∈ B, r.IsSymmetric := by
    have : B ≤ symmetricSubalgebra (Fin n) ℂ :=
      Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
    exact fun r hr => this hr
  have hclose : ∀ i : Fin n, TopClose ((i : ℕ) + 1) (psumFin i) (q i) := by
    intro i
    have h1 : (psumFin i).totalDegree ≤ (i : ℕ) + 1 :=
      (isHomogeneous_psum _).totalDegree_le
    refine ⟨h1, ?_, Or.inr ?_⟩
    · have : q i = psumFin i + (q i - psumFin i) := by ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le h1 (hdeg i).le)
    · rw [← neg_sub, totalDegree_neg]; exact hdeg i
  induction d with
  | zero =>
    intro p _ hp
    rw [totalDegree_eq_zero_iff_eq_C.1 (show p.totalDegree = 0 by omega)]
    exact B.algebraMap_mem _
  | succ d ih =>
    intro p hp hpd
    obtain ⟨F, rfl⟩ : ∃ F, aeval psumFin F = p := by
      have := mem_adjoin_psum_of_isSymmetric hp
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    set P : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => psumFin i ^ k
    set Q : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => q i ^ k
    have hPhom : ∀ c, (P c).IsHomogeneous (psumWt c) := by
      intro c
      simp only [P, Finsupp.prod, psumWt]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      rw [mul_comm]
      exact (isHomogeneous_psum _).pow _
    have hPQ : ∀ c, TopClose (psumWt c) (P c) (Q c) := by
      intro c
      simp only [P, Q, Finsupp.prod, psumWt]
      exact TopClose.prod _ _ _ _ fun i _ => (hclose i).pow (c i)
    have hF : aeval psumFin F = ∑ c ∈ F.support, AddMonoidAlgebra.coeff F c • P c := by
      conv_lhs => rw [F.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [aeval_monomial, Algebra.smul_def]
    set S := F.support.filter fun c => psumWt c = d + 1
    set r := ∑ c ∈ S, AddMonoidAlgebra.coeff F c • Q c
    have hr : r ∈ B := by
      refine B.sum_mem fun c _ => B.smul_mem ?_ _
      simp only [Q, Finsupp.prod]
      exact B.prod_mem fun i _ => B.pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _
    have htop : homogeneousComponent (d + 1) (aeval psumFin F) = ∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, map_sum, sum_filter]
      refine sum_congr rfl fun c _ => ?_
      rw [map_smul, homogeneousComponent_of_mem (hPhom c)]
      by_cases h : psumWt c = d + 1
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
    have hlow : (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F)).totalDegree ≤ d := by
      set p := aeval psumFin F
      rw [totalDegree, Finset.sup_le_iff]
      intro m hm
      rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
      have hm' : m ∈ p.support := by
        rw [mem_support_iff]; intro h0; rw [h0] at hm; simp at hm
      have h1 := le_totalDegree hm'
      by_cases hd : m.degree = d + 1
      · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
      · have : (m.sum fun _ e => e) = m.degree := by
          rfl
        rw [this] at h1 ⊢
        omega
    have hdiff : (∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c - r).totalDegree ≤ d := by
      rw [← sum_sub_distrib]
      refine totalDegree_finsetSum_le fun c hc => ?_
      rw [← smul_sub]
      refine (totalDegree_smul_le _ _).trans ?_
      have hwc : psumWt c = d + 1 := (mem_filter.1 hc).2
      rcases (hPQ c).2.2 with h | h
      · rw [h, sub_self, totalDegree_zero]; exact Nat.zero_le _
      · rw [hwc] at h; omega
    have hkey : (aeval psumFin F - r).totalDegree ≤ d := by
      have : aeval psumFin F - r = (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F))
          + (∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c - r) := by rw [htop]; ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le hlow hdiff)
    have hsym : (aeval psumFin F - r).IsSymmetric :=
      (symmetricSubalgebra (Fin n) ℂ).sub_mem hp (hBsym r hr)
    have := B.add_mem (ih _ hsym hkey) hr
    rwa [sub_add_cancel] at this

theorem adjoin_eq_symmetricSubalgebra (q : Fin n → MvPolynomial (Fin n) ℂ)
    (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) :
    Algebra.adjoin ℂ (Set.range q) = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · exact Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
  · intro p hp
    exact symmetric_le_adjoin q hq hdeg _ p hp le_rfl

end GroundTheory.Automorphic.HarishChandra
end

