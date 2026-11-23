module

public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.MinorExpLt
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

private theorem cmIdx_val_eq {r n : ℕ} (v : Fin r × Fin n) :
    ((cmIdx r n v : Fin (n * r)) : ℕ) = v.1.val + r * v.2.val := by
  first
  | rfl
  | (simp only [cmIdx, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, finProdFinEquiv_apply_val]; done)
  | (simp [cmIdx, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]; done)
  | (simp [cmIdx]; ring)

private theorem col_lt_or_col_eq_row_lt_of_cmIdx_lt {r n : ℕ} {v w : Fin r × Fin n}
    (h : cmIdx r n v < cmIdx r n w) :
    v.2.val < w.2.val ∨ (v.2 = w.2 ∧ v.1 < w.1) := by
  have h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ) := h
  rw [cmIdx_val_eq, cmIdx_val_eq] at h0
  have hv1 := v.1.isLt
  have hw1 := w.1.isLt
  rcases lt_trichotomy v.2.val w.2.val with h1 | h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨Fin.ext h1, ?_⟩
    rw [h1] at h0
    show v.1.val < w.1.val
    omega
  · exfalso
    have hm : r * (w.2.val + 1) ≤ r * v.2.val := by
      first
      | exact Nat.mul_le_mul_left r h1
      | exact Nat.mul_le_mul_left h1 r
      | exact Nat.mul_le_mul (le_refl r) h1
    rw [Nat.mul_add, Nat.mul_one] at hm
    first
    | omega
    | linarith

private theorem domCongr_cmIdx_apply_cmIdx {r n : ℕ} (x : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    (Finsupp.domCongr (cmIdx r n) x) (cmIdx r n v) = x v := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])
  | (simp; done)

private theorem sum_single_castLE_apply' {r n s : ℕ} (τ : Fin s → Fin r) (hs : s ≤ n) (b : Fin r) (t : Fin n) :
    (∑ q : Fin s, Finsupp.single (τ q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
      if h : t.val < s then (if τ ⟨t.val, h⟩ = b then 1 else 0) else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases h : t.val < s
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨t.val, h⟩]
    · rw [Finsupp.single_apply]
      by_cases hb : τ ⟨t.val, h⟩ = b
      · have hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t) := by
          first
          | exact Prod.ext hb (Fin.ext rfl)
          | exact Prod.ext_iff.2 ⟨hb, Fin.ext rfl⟩
          | (subst hb; rfl)
        rw [if_pos hp, if_pos hb]
      · rw [if_neg, if_neg hb]
        intro he
        exact hb (congrArg Prod.fst he)
    · intro q _ hq
      rw [Finsupp.single_apply, if_neg]
      intro he
      apply hq
      apply Fin.ext
      have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
      exact h2
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply h
    have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
    have h3 := q.isLt
    have h4 : (Fin.castLE hs q).val = q.val := rfl
    omega

private theorem toLex_lt_of_eq_below_of_apply_lt {N : ℕ} (x y : Fin N →₀ ℕ) (i : Fin N)
    (h1 : ∀ j, j < i → x j = y j) (h2 : x i < y i) : toLex x < toLex y := by
  first
  | exact ⟨i, h1, h2⟩
  | exact Finsupp.Lex.lt_of_forall_lt_of_lt _ _ i h1 h2
  | (show Finsupp.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (show Pi.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (rw [Finsupp.lex_def]; exact ⟨i, h1, h2⟩)

private theorem colLex_lt_of_toLex_domCongr_cmIdx_lt {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ}
    (h : toLex (Finsupp.domCongr (cmIdx r n) c) <
      toLex (Finsupp.domCongr (cmIdx r n) d)) :
    c ≺[colLex r n] d := h

theorem minorExponentLt : MinorExpLt := by
  intro r n s I hs hI σ hσ
  have hex : ∃ q, σ q ≠ q := by
    by_contra h
    push_neg at h
    apply hσ
    ext x
    first
    | (rw [h x]; rfl)
    | simp [h x]
  obtain ⟨q0, hq0, hmin⟩ := (wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex
  have hq0' : σ q0 ≠ q0 := hq0
  have hfix : ∀ q, q < q0 → σ q = q := fun q hq => by
    by_contra h
    exact hmin q h hq
  have hgt : q0 < σ q0 := by
    rcases lt_trichotomy (σ q0) q0 with h | h | h
    · exact absurd (σ.injective (hfix _ h)) h.ne
    · exact absurd h hq0'
    · exact h
  have hIlt : I q0 < I (σ q0) := hI hgt
  have hA : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t
  have hB : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' I hs b t
  have hcq : (Fin.castLE hs q0).val = q0.val := rfl
  have ht0 : (Fin.castLE hs q0).val < s := q0.isLt
  have e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0 := Fin.ext rfl
  apply colLex_lt_of_toLex_domCongr_cmIdx_lt
  apply toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))
  · intro j hj
    obtain ⟨v, rfl⟩ := (cmIdx r n).surjective j
    rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]
    obtain ⟨b, t⟩ := v
    rw [hA, hB]
    have hlt := col_lt_or_col_eq_row_lt_of_cmIdx_lt hj
    try dsimp only at hlt
    rcases hlt with hlt | ⟨rfl, hb⟩
    · have ht : t.val < s := by
        have := q0.isLt
        omega
      have hlt' : (⟨t.val, ht⟩ : Fin s) < q0 := by
        show t.val < q0.val
        omega
      rw [dite_eq_left ht, dite_eq_left ht, hfix _ hlt']
    · rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']
  · rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]
    rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]
    exact Nat.zero_lt_one

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowdiv_mem_dualWeyl_iff (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def CoeffHom {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ : Fin n → ℕ) : Prop :=
  ∀ k, IsWeightedHomogeneous (colW r n) (P.coeff k) μ

theorem CoeffHom.mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' : Fin n → ℕ}
    (hP : CoeffHom P μ) (hQ : CoeffHom Q μ') : CoeffHom (P * Q) (μ + μ') := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)

theorem CoeffHom.one {R : Type*} [CommRing R] {r n : ℕ} :
    CoeffHom (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one R _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ : Fin n → ℕ}
    (hP : CoeffHom P μ) (e : ℕ) : CoeffHom (P ^ e) (e • μ) := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact CoeffHom.one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem CoeffHom.prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin n → ℕ)
    (h : ∀ i ∈ s, CoeffHom (P i) (μ i)) : CoeffHom (∏ i ∈ s, P i) (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem CoeffHom.algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    CoeffHom (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs
  · rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    CoeffHom (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (colW r n v) := by
  intro k
  have hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v) :=
    isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (colW r n v) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    CoeffHom (rowGen R a b (monomial d c)) (Finsupp.weight (colW r n) d) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine (CoeffHom.algebraMap c).mul ?_
  unfold Finsupp.prod Finsupp.sum
  exact CoeffHom.prod _ _ _ fun v _ => (CoeffHom.gen a b v).pow _

theorem rowDiv_homog (R : Type*) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) :
    IsWeightedHomogeneous (colW r n) (rowDiv R a b k f) ν := by
  unfold rowDiv
  conv => pattern f; rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := CoeffHom.rowGen_monomial R a b d (AddMonoidAlgebra.coeff f d) k
  rwa [hf (mem_support_iff.mp hd)] at this

def rowGenO (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R]
      Polynomial (MvPolynomial (Option (Fin r × Fin n)) R) :=
  aeval fun o => Option.elim o (Polynomial.C (X none)) fun v =>
    Polynomial.C (X (some v)) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (some (a, v.2))) else 0)

theorem rowGenO_comp_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (l j : Fin n) :
    (rowGenO R a b).comp (colAddGen R (r := r) l j) =
      (Polynomial.mapAlgHom (colAddGen R (r := r) l j)).comp (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h2 : v.2 = j <;> by_cases h1 : v.1 = b <;>
    simp [h1, h2, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      aeval_X] <;> ring

theorem rowGenO_comp_rename (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    (rowGenO R a b).comp (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      (Polynomial.mapAlgHom (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n)))).comp
        (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h1 : v.1 = b <;>
    simp [h1, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]

theorem rowDiv_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : colAddGen R l j f = rename some f) :
    colAddGen R l j (rowDiv R a b k f) = rename some (rowDiv R a b k f) := by
  have hA := congrArg (fun φ => φ f) (rowGenO_comp_colAddGen R a b l j)
  have hB := congrArg (fun φ => φ f) (rowGenO_comp_rename R (n := n) a b)
  simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom] at hA hB
  rw [hf, hB] at hA
  have hk := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P k) hA
  simp only [Polynomial.coeff_map] at hk
  unfold rowDiv
  exact hk.symm

theorem dualWeylModuleRowDividedPowerStable : RowDivStable := by
  intro R _ r n ν a b k f hf
  rw [rowdiv_mem_dualWeyl_iff] at hf ⊢
  exact ⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem rowDiv_add_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add (f := _), Polynomial.coeff_add]

private theorem rowDiv_smul_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem weylModuleRowDividedPowerStable : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := rowDiv_add_fock_space_tableaux R a b k
      map_smul' := rowDiv_smul_fock_space_tableaux R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf

end Formalism.GradedWeylDivisibility
end
end

