module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
public import Lemmata.MiscLemmasH.Imports
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CompleteOfBasis
section
set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Complete

variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)


end Complete

section Lift

variable {A : Type} [CommRing A] (I : Ideal A)

theorem lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)

theorem idem_zero [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _

end Lift

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.DetNeZeroOfChars
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Chars

variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]

theorem char_indep (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) (c : ι' → L) (hc : ∀ i, ∑ j, c j * χ j (b i) = 0) :
    c = 0 := by
  have key : ∀ x : A, ∑ j, c j * χ j x = 0 := by
    intro x
    obtain ⟨r, hr⟩ := hb x
    have hx : ∀ j, χ j x = ∑ i, φ (r i) * χ j (b i) := by
      intro j
      have h1 : χ j (e * x) = χ j x := by rw [map_mul, he, one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h1, hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hφ]
    calc ∑ j, c j * χ j x = ∑ j, ∑ i, c j * (φ (r i) * χ j (b i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hx j, Finset.mul_sum]
      _ = ∑ i, φ (r i) * ∑ j, c j * χ j (b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by simp [hc]
  have hli : LinearIndependent L (fun j => ((χ j).toMonoidHom : A → L)) := by
    have h := (linearIndependent_monoidHom A L).comp (fun j => (χ j).toMonoidHom) (by
      intro j k hjk
      apply hχ
      ext x
      exact DFunLike.congr_fun hjk x)
    exact h
  funext j
  have h2 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    rw [Finset.sum_apply]
    exact key x)
  exact h2 j

theorem card_le_of_chars (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by
  have hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := char_indep χ hχ φ hφ e he b hb g (fun i => by
      have h3 := congrFun hg i
      rw [Finset.sum_apply] at h3
      exact h3)
    intro j
    simp [h0]
  simpa using hli.fintype_card_le_finrank

theorem det_ne_zero_of_chars [DecidableEq ι] (χ : ι → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : (Matrix.of fun i j => χ j (b i)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply char_indep χ hχ φ hφ e he b hb v
  intro i
  have h := congrFun hv i
  calc ∑ j, v j * χ j (b i) = ∑ j, χ j (b i) * v j :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := by
        first
        | exact h
        | simpa [Matrix.mulVec, dotProduct] using h

end Chars

section Label

end Label

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePHaDefs
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

def SatRetrSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : Submodule ℤ (ι → ℤ)), (∀ (z : ℤ) (x : ι → ℤ), z ≠ 0 → z • x ∈ W → x ∈ W) →
    ∃ ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ x, ρ x ∈ W) ∧ ∀ x ∈ W, ρ x = x

def RowInvUpSt : Prop :=
  ∀ (Ty : Type) (r : Ty → ℕ) (n : ℕ) (K : Type) [Field K] [CharZero K] (P : MvPolynomial (Letter Ty r n) K),
    (∀ (σ : Ty) (i i' : Fin (r σ)), i' < i → ∀ q : ℚ, rowShift r n K σ i i' (q : K) P = P) → RowInv r n K P

end Formalism.L2.FormalSeriesBounds.HaP
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJoint
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

section Eig

variable {C : Type} [Field C] [CharZero C] {n : ℕ}

theorem sq_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (u : Fin n → C)
    (h2 : Matrix.mulVec t (Matrix.mulVec t u - μ • u) = μ • (Matrix.mulVec t u - μ • u)) :
    Matrix.mulVec t u = μ • u := by
  set x := Matrix.mulVec t u - μ • u with hxdef
  have htu : Matrix.mulVec t u = μ • u + x := by rw [hxdef]; abel
  have hx : ∀ k : ℕ, Matrix.mulVec (t ^ k) x = μ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' t k, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h2, smul_smul, ← pow_succ]
  have hu : ∀ k : ℕ, Matrix.mulVec (t ^ (k + 1)) u = μ ^ (k + 1) • u + (((k : C) + 1) * μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp [htu]
    | succ k ih =>
      rw [pow_succ' t (k + 1), ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, htu, h2]
      push_cast
      module
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hA := hu (r + 1)
  rw [show r + 1 + 1 = r + 2 from rfl, ht, htu] at hA
  have hB := hx (r + 2)
  rw [ht, h2] at hB
  suffices hx0 : x = 0 by rw [htu, hx0, add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp at hA
    exact hA
  · have hB' : (μ ^ (r + 2) - μ) • x = 0 := by rw [sub_smul, ← hB, sub_self]
    rcases smul_eq_zero.mp hB' with h | h
    · have h1 : μ ^ (r + 1) = 1 := by
        have e1 : μ ^ (r + 1) * μ = 1 * μ := by
          rw [← pow_succ, one_mul]
          exact sub_eq_zero.mp h
        exact mul_right_cancel₀ hμ e1
      rw [sub_eq_zero.mp h, h1, mul_one] at hA
      have hA2 := add_left_cancel hA
      have e : (((r + 1 : ℕ) : C) + 1) • x = ((r : C) + 1) • x + x := by
        push_cast
        rw [add_smul, one_smul]
      rw [e] at hA2
      have h3 : ((r : C) + 1) • x = 0 := add_eq_right.mp hA2.symm
      exact (smul_eq_zero.mp h3).resolve_left (Nat.cast_add_one_ne_zero r)
    · exact h

theorem gen_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (w : Fin n → C)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' t : Module.End C (Fin n → C)) μ) : Matrix.mulVec t w = μ • w := by
  rw [Module.End.mem_maxGenEigenspace] at hw
  obtain ⟨k, hk⟩ := hw
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    subst hk
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hk
    have hy := ih _ hk
    have e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w := by
      simp [Matrix.toLin'_apply]
    rw [e] at hy
    exact sq_to_eig hq t ht μ w hy

end Eig

theorem jointEig_holds : JointEigSt := by
  intro C _ _ hC n q hq T hT hcomm v
  let f : T → Module.End C (Fin n → C) := fun t => Matrix.toLin' t.1
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => by
      show (Matrix.toLin' i.1).comp (Matrix.toLin' j.1) = (Matrix.toLin' j.1).comp (Matrix.toLin' i.1)
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i.1 i.2 j.1 j.2])
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hv : v ∈ ⨆ χ : T → C, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun v => ∃ (m : ℕ) (w : Fin m → Fin n → C),
    v = ∑ j, w j ∧ ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j) hv ?_ ?_ ?_
  · intro χ x hx
    refine ⟨1, fun _ => x, by simp, fun _ t ht => ⟨χ ⟨t, ht⟩, gen_to_eig hq t (hT t ht) _ x ?_⟩⟩
    exact (Submodule.mem_iInf _).mp hx ⟨t, ht⟩
  · exact ⟨0, Fin.elim0, by simp, fun j => Fin.elim0 j⟩
  · rintro x y ⟨m₁, w₁, rfl, h₁⟩ ⟨m₂, w₂, rfl, h₂⟩
    refine ⟨m₁ + m₂, Fin.append w₁ w₂, by rw [Fin.sum_univ_add]; simp, fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using h₁ j
    · simpa using h₂ j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial Matrix

section Sep

variable {K : Type} [Field K] [CharZero K]

theorem aff_sub (α β : K) (h : α ≠ 0 ∨ β ≠ 0) : {t : ℕ | α + (t : K) * β = 0}.Subsingleton := by
  intro t1 h1 t2 h2
  simp only [Set.mem_setOf_eq] at h1 h2
  by_cases hb : β = 0
  · rw [hb, mul_zero, add_zero] at h1
    exact absurd h1 (h.resolve_right (not_not.mpr hb))
  · have h3 : ((t1 : K) - t2) * β = 0 := by linear_combination h1 - h2
    have h4 : (t1 : K) = t2 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb)
    exact_mod_cast h4

theorem exists_sep {O : Type} [CommRing O] {ι : Type} [Fintype ι] (em : ι → (O →+* K))
    (hem : Function.Injective em) : ∃ x0 : O, ∀ c c', c ≠ c' → em c x0 ≠ em c' x0 := by
  classical
  have key : ∀ F : Finset (ι × ι), (∀ q ∈ F, q.1 ≠ q.2) → ∃ x0 : O, ∀ q ∈ F, em q.1 x0 ≠ em q.2 x0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert p F _ ih =>
      intro hF
      obtain ⟨x, hx⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
      obtain ⟨z, hz⟩ : ∃ z, em p.1 z ≠ em p.2 z := by
        by_contra h
        push Not at h
        exact hF p (Finset.mem_insert_self p F) (hem (RingHom.ext h))
      have hfin : (⋃ q ∈ ((↑(insert p F) : Set (ι × ι))),
          {t : ℕ | (em q.1 x - em q.2 x) + (t : K) * (em q.1 z - em q.2 z) = 0}).Finite := by
        refine Set.Finite.biUnion (Finset.finite_toSet _) fun q hq => (aff_sub _ _ ?_).finite
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hq) with rfl | hq'
        · exact Or.inr (sub_ne_zero.2 hz)
        · exact Or.inl (sub_ne_zero.2 (hx q hq'))
      obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
      refine ⟨x + (t : O) * z, fun q hq h => ht (Set.mem_biUnion (Finset.mem_coe.2 hq) ?_)⟩
      simp only [Set.mem_ofPred_eq]
      simp only [map_add (f := _), map_mul, map_natCast] at h
      linear_combination h
  obtain ⟨x0, hx0⟩ := key (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  exact ⟨x0, fun c c' hcc' => hx0 (c, c') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcc'⟩)⟩

end Sep

section Mat

variable {K : Type} [Field K] {n : ℕ}

theorem alg_mulVec (a : K) (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a * A) *ᵥ w = a • (A *ᵥ w) := by
  rw [← Algebra.smul_def, Matrix.smul_mulVec]

theorem alg_mulVec1 (a : K) (w : Fin n → K) :
    algebraMap K (Matrix (Fin n) (Fin n) K) a *ᵥ w = a • w := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem commute_aeval {A B : Matrix (Fin n) (Fin n) K} (h : Commute A B) (f : K[X]) : Commute A (aeval B f) := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (Algebra.commutes a A).symm
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add_right hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h

theorem pow_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (k : ℕ) :
    (N + B) ^ k *ᵥ w = (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k *ᵥ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.add_mulVec, Matrix.add_mulVec]
    congr 1
    have hc : Commute N ((algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k) :=
      ((show Commute (algebraMap K (Matrix (Fin n) (Fin n) K) lam) N from Algebra.commutes lam N).symm.add_right
        hNB).pow_right k
    rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, alg_mulVec1]

theorem aeval_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (f : K[X]) :
    aeval (N + B) f *ᵥ w = aeval (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) f *ᵥ w := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, Matrix.add_mulVec, hp, hq]
  | monomial k a _ =>
    rw [map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow, aeval_X, aeval_X, alg_mulVec, alg_mulVec,
      pow_shift N B hNB lam w hw (k + 1)]

theorem X_sub_mul_basis {ι : Type} [DecidableEq ι] {s : Finset ι} {v : ι → K} {i : ι} (hi : i ∈ s) :
    (X - Polynomial.C (v i)) * Lagrange.basis s v i =
      Polynomial.C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.nodal_eq_mul_nodal_erase hi]
  simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, Lagrange.nodalWeight, Lagrange.nodal,
    map_prod]
  ring

theorem coeff_extract [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) (a μ : ι → K) (c : ι) (hac : a c = 0) (ha : ∀ c', c' ≠ c → a c' ≠ 0)
    (h : ∀ t : ℕ, aeval B (∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c')))) *ᵥ w = 0) :
    B *ᵥ w = μ c • w := by
  set R : K[X][X] := ∏ c', (Polynomial.C (Polynomial.C (a c')) + X * Polynomial.C (X - Polynomial.C (μ c'))) with hR
  have hev : ∀ t : ℕ, R.eval (Polynomial.C (t : K)) =
      ∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c'))) := by
    intro t
    rw [hR, eval_prod]
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, eval_C]
  have hcoord : ∀ i, (aeval B (R.coeff 1) *ᵥ w) i = 0 := by
    intro i
    set q : K[X] := ∑ k ∈ Finset.range (R.natDegree + 2), monomial k ((aeval B (R.coeff k) *ᵥ w) i) with hq
    have hroot : ∀ t : ℕ, q.eval (t : K) = 0 := by
      intro t
      have h1 := congrFun (h t) i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hev t, eval_eq_sum_range' (n := R.natDegree + 2) (by omega), map_sum, Matrix.sum_mulVec,
        Finset.sum_apply, Pi.zero_apply] at h1
      rw [hq, eval_finsetSum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
      rw [eval_monomial, ← map_pow, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
      rintro _ ⟨t, rfl⟩
      exact hroot t
    have hc1 := congrArg (fun p : K[X] => p.coeff 1) hq0
    simp only [hq, finsetSum_coeff, coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range, coeff_zero] at hc1
    rw [if_pos (by omega)] at hc1
    exact hc1
  have hR1 : R.coeff 1 = (X - Polynomial.C (μ c)) * Polynomial.C (∏ c' ∈ Finset.univ.erase c, a c') := by
    rw [hR, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), hac, map_zero, map_zero, zero_add, mul_assoc]
    refine (coeff_X_mul _ 0).trans ?_
    rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero]
  have hπ : ∏ c' ∈ Finset.univ.erase c, a c' ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c' hc' => ha c' (Finset.ne_of_mem_erase hc')
  have hv : aeval B (R.coeff 1) *ᵥ w = 0 := funext hcoord
  rw [hR1, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, map_sub, aeval_X, aeval_C, Matrix.sub_mulVec,
    alg_mulVec1] at hv
  have h2 := (smul_eq_zero.1 hv).resolve_left hπ
  rwa [sub_eq_zero] at h2

end Mat

theorem split_holds : SplitSt := by
  intro K _ _ O _ n ι _ _ M P em hPP hPM hinj hann v
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hP : P = 0 := by
      have h := hann 0
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_mul] at h
      exact h
    refine ⟨fun c => (hι.false c).elim, ?_, fun c => (hι.false c).elim⟩
    rw [hP, Matrix.zero_mulVec, Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨x0, hx0⟩ := exists_sep em hinj
  have hinjl : Set.InjOn (fun c => em c x0) (Finset.univ : Finset ι) := fun c _ c' _ h => by
    by_contra hne
    exact hx0 c c' hne h
  refine ⟨fun c => P *ᵥ (aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← Matrix.mulVec_sum, ← Matrix.sum_mulVec, ← map_sum, Lagrange.sum_basis hinjl Finset.univ_nonempty, map_one,
      Matrix.one_mulVec]
  intro c x
  set u := aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v with hu
  have hP0 : Commute P (M x0) := hPM x0

  have hXL : (X - Polynomial.C (em c x0)) * Lagrange.basis Finset.univ (fun c => em c x0) c =
      Polynomial.C (Lagrange.nodalWeight Finset.univ (fun c => em c x0) c) * ∏ c', (X - Polynomial.C (em c' x0)) :=
    by
      simpa only [Lagrange.nodal_eq] using
        (X_sub_mul_basis (v := fun c' => em c' x0) (Finset.mem_univ c))
  have hE0 : (M x0 - algebraMap K _ (em c x0)) *
      (P * aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c)) = 0 := by
    have e1 : M x0 - algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) = aeval (M x0) (X - Polynomial.C (em c x0)) := by
      rw [map_sub, aeval_X, aeval_C]
    rw [e1, ← mul_assoc, ← (commute_aeval hP0 _).eq, mul_assoc, ← map_mul, hXL, map_mul, aeval_C, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, (commute_aeval hP0 _).eq, hann x0, mul_zero]
  have hw0 : M x0 *ᵥ (P *ᵥ u) = em c x0 • (P *ᵥ u) := by
    have h1 := congrArg (fun A => A *ᵥ v) hE0
    simp only [Matrix.zero_mulVec] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, alg_mulVec1, sub_eq_zero] at h1
    exact h1

  refine coeff_extract (M x) (P *ᵥ u) (fun c' => em c x0 - em c' x0) (fun c' => em c' x) c (sub_self _)
    (fun c' hc' => sub_ne_zero.2 (hx0 c c' (Ne.symm hc'))) fun t => ?_
  have hcx : Commute (M x0) ((t : Matrix (Fin n) (Fin n) K) * M x) := by
    refine ((Nat.cast_commute t (M x0)).symm).mul_right ?_
    show M x0 * M x = M x * M x0
    rw [← map_mul, ← map_mul, mul_comm]
  have h1 := congrArg (fun A => A *ᵥ u) (hann (x0 + (t : O) * x))
  simp only [Matrix.zero_mulVec] at h1
  rw [← Matrix.mulVec_mulVec, map_add (f := _), map_mul, map_natCast, aeval_shift _ _ hcx (em c x0) _ hw0] at h1
  have e2 : algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) + (t : Matrix (Fin n) (Fin n) K) * M x =
      aeval (M x) (Polynomial.C (em c x0) + Polynomial.C (t : K) * X) := by
    rw [map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, map_natCast]
  rw [e2, ← aeval_comp, prod_comp] at h1
  refine Eq.trans ?_ h1
  congr 2
  refine Finset.prod_congr rfl fun c' _ => ?_
  rw [sub_comp, X_comp, C_comp]
  simp only [map_add (f := _), map_mul, map_natCast, map_sub]
  ring

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end

