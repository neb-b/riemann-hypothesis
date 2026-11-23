module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations
section
namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

theorem derivation_aeval_eq {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, pderiv_X, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [map_add (f := _), map_mul, aeval_X, apply_ite (aeval z), map_zero, map_one, add_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring

theorem totalDegree_pderiv_lt {K ι : Type*} [CommRing K] (P : MvPolynomial ι K) (i : ι)
    (hP : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hsum : pderiv i P = ∑ m ∈ P.support, pderiv i (monomial m (AddMonoidAlgebra.coeff P m)) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [hsum]
  refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_lt_iff hP]
  intro m hm
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi, hP]
  · have hm1 : m = (m - Finsupp.single i 1) + Finsupp.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have key : ((m - Finsupp.single i 1).sum fun _ e => e) + 1 = m.sum fun _ e => e := by
      conv_rhs => rw [hm1]
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl]
    have hle : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
    show ((m - Finsupp.single i 1).sum fun _ e => e) < _
    omega

theorem eq_C_of_pderiv_eq_zero {K ι : Type*} [Field K] [CharZero K] (P : MvPolynomial ι K)
    (h : ∀ i, pderiv i P = 0) : P.totalDegree = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
    (Finset.nonempty_of_ne_empty (by rintro hs; apply hne; simp [totalDegree, hs]))
    (fun s => s.sum fun _ e => e)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [totalDegree] using hmd
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (Finsupp.ext hc)
  have hc := congrArg (AddMonoidAlgebra.coeff · (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hk]
  rw [hm'] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact (mem_support_iff.mp hm) h1
  · exact Nat.cast_add_one_ne_zero _ h1

theorem algebraicIndependent_of_derivations {K R ι J : Type*} [Field K] [CharZero K] [CommRing R]
    [Nontrivial R] [Algebra K R] [Fintype ι] (z : ι → R) (δ : J → Derivation K R R)
    (h : ∀ c : ι → R, (∀ j, ∑ i, c i * δ j (z i) = 0) → ∀ i, c i = 0) :
    AlgebraicIndependent K z := by
  classical
  rw [algebraicIndependent_iff]
  suffices H : ∀ n (P : MvPolynomial ι K), P.totalDegree = n → aeval z P = 0 → P = 0 from
    fun P => H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have hd : ∀ i, pderiv i P = 0 := by
    have hv : ∀ i, aeval z (pderiv i P) = 0 :=
      h (fun i => aeval z (pderiv i P)) (fun j => by rw [← derivation_aeval_eq, hP, map_zero])
    intro i
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0]
      simp
    · exact ih _ (hn ▸ totalDegree_pderiv_lt P i (Nat.pos_of_ne_zero h0)) _ rfl (hv i)
  have h0 := eq_C_of_pderiv_eq_zero P hd
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, aeval_C] at hP
  have hc : AddMonoidAlgebra.coeff P 0 = 0 := (algebraMap K R).injective (hP.trans (map_zero _).symm)
  rw [h0, hc, map_zero]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.BWPolyA
section
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_poly_eq_of_eval_eq_off (P Q : ℂ[X]) (E : Set ℂ) (hE : E.Finite)
    (h : ∀ t ∉ E, P.eval t = Q.eval t) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun t ht => h t ht) hE.infinite_compl

theorem bwp_finite_eval_eq_zero {P : ℂ[X]} (hP : P ≠ 0) : {t : ℂ | P.eval t = 0}.Finite :=
  Polynomial.finite_setOfPred_isRoot hP

theorem bwp_exists_nodes (E : Set ℂ) (hE : E.Finite) (k : ℕ) :
    ∃ S : Finset ℂ, S.card = k + 1 ∧ ∀ c ∈ S, c ∉ E := by
  obtain ⟨S, hS, hcard⟩ := hE.infinite_compl.exists_subset_card_eq (k + 1)
  exact ⟨S, hcard, fun c hc => hS hc⟩

theorem bwp_eval_eq_lagrange (S : Finset ℂ) (Q : ℂ[X]) (k : ℕ) (hS : S.card = k + 1)
    (hQ : Q.natDegree ≤ k) (x : ℂ) :
    Q.eval x = ∑ c ∈ S, (Lagrange.basis S id c).eval x * Q.eval c := by
  have hinj : Set.InjOn id (S : Set ℂ) := Function.injective_id.injOn
  have hdeg : Q.degree < S.card := by
    rw [hS]
    calc Q.degree ≤ (k : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hQ
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [mul_comm]

theorem bwp_eval_aeval_X {σ : Type*} (L : ℂ[X]) (i : σ) (y : σ → ℂ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) L) = L.eval (y i) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem bwp_sepPoly_fin (k : ℕ) : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) →
    ∃ F : MvPolynomial (Fin n) ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  intro n
  induction n with
  | zero =>
    intro G _
    exact ⟨MvPolynomial.C (G 0), fun y => by
      rw [MvPolynomial.eval_C, Subsingleton.elim y 0]⟩
  | succ n ih =>
    intro G hG
    obtain ⟨S, hS, -⟩ := bwp_exists_nodes ∅ Set.finite_empty k
    have hsub : ∀ c : ℂ, ∃ F : MvPolynomial (Fin n) ℂ,
        ∀ y', G (Fin.cons c y') = MvPolynomial.eval y' F := by
      intro c
      refine ih (fun y' => G (Fin.cons c y')) ?_
      intro y' m
      obtain ⟨Q, hQ, hQt⟩ := hG (Fin.cons c y') m.succ
      exact ⟨Q, hQ, fun t => by simp only [Fin.cons_update]; exact hQt t⟩
    choose Fc hFc using hsub
    refine ⟨∑ c ∈ S, Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis S id c) *
      MvPolynomial.rename Fin.succ (Fc c), fun y => ?_⟩
    obtain ⟨Q, hQ, hQt⟩ := hG y 0
    have hy : ∀ t, Function.update y 0 t = Fin.cons t (Fin.tail y) := by
      intro t
      conv_lhs => rw [← Fin.cons_self_tail y]
      exact Fin.update_cons_zero _ _ _
    have h1 : G y = Q.eval (y 0) := by
      rw [← hQt]; simp
    rw [h1, bwp_eval_eq_lagrange S Q k hS hQ, MvPolynomial.eval_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_mul, bwp_eval_aeval_X, MvPolynomial.eval_rename, ← hQt c, hy c, hFc c]
    rfl

theorem bwp_sepPoly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (G : (σ → ℂ) → ℂ)
    (hG : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  obtain ⟨F, hF⟩ := bwp_sepPoly_fin k (Fintype.card σ) (fun z => G (z ∘ e)) (fun z m => by
    obtain ⟨Q, hQd, hQ⟩ := hG (z ∘ e) (e.symm m)
    refine ⟨Q, hQd, fun t => ?_⟩
    show G ((Function.update z m t) ∘ e) = _
    rw [Function.update_comp_equiv, hQ])
  refine ⟨MvPolynomial.rename e.symm F, fun y => ?_⟩
  rw [MvPolynomial.eval_rename, ← hF]
  congr 1
  ext s
  simp

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.DetGramEqProdGramSchmidt
section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset InnerProductSpace

private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩

theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, hc j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp

theorem prod_le_re_det_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod₀ (fun k _ => hδ k) (fun k _ => ?_)
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  have hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h1 := h k _ hmem
  rwa [← eq_sub_of_add_eq (hc k).symm] at h1

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.GaussIndepOfLeTrdeg
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

private theorem exists_transcendenceBasis_subset_adjoin_range {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : ∃ t ⊆ ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))),
      IsTranscendenceBasis E (Subtype.val : t → Algebra.adjoin E (Set.range tb)) := by
  have htop : Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  haveI : Algebra.IsAlgebraic
      (Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))))
      (Algebra.adjoin E (Set.range tb)) := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
      rw [htop]; exact Algebra.mem_top
    exact isAlgebraic_algebraMap (⟨a, ha⟩ : Algebra.adjoin E _)⟩
  exact exists_isTranscendenceBasis_subset (R := E) _

theorem gauss_trdeg_adjoin_le {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) ≤ Cardinal.mk σ := by
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
        Cardinal.mk_le_mk_of_subset hts
    _ ≤ Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
    _ ≤ Cardinal.mk σ := Cardinal.mk_range_le

theorem gauss_card_le_trdeg_add {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] [IsScalarTower F E C] {σ τ : Type} (tb : σ → C) (ub : τ → C)
    (hu : AlgebraicIndependent F ub) (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) :
    Cardinal.mk τ ≤ Algebra.trdeg F E + Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) := by
  haveI : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).mpr (algebraMap F E).injective
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  rw [trdeg_add_eq F E (A := Algebra.adjoin E (Set.range tb))]
  have hu' : AlgebraicIndependent F (fun j => (⟨ub j, hmem j⟩ : Algebra.adjoin E (Set.range tb))) :=
    AlgebraicIndependent.of_comp ((Algebra.adjoin E (Set.range tb)).val.restrictScalars F) hu
  exact hu'.cardinalMk_le_trdeg

theorem gauss_indep_of_le_trdeg {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    [Finite σ] (tb : σ → C)
    (h : Cardinal.mk σ ≤ Algebra.trdeg E (Algebra.adjoin E (Set.range tb))) :
    AlgebraicIndependent E tb := by
  classical
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  have ht := hb.cardinalMk_eq_trdeg
  have h1 : Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
    Cardinal.mk_le_mk_of_subset hts
  have h2 : Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) ≤
      Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
  have h3 : Cardinal.mk (Set.range tb) ≤ Cardinal.mk σ := Cardinal.mk_range_le
  have hσt : Cardinal.mk σ ≤ Cardinal.mk t := ht ▸ h

  have hinj : Function.Injective tb := by
    obtain ⟨e⟩ := Cardinal.eq.1 (le_antisymm h3 (hσt.trans (h1.trans h2)))
    have hr : Function.Injective (Set.rangeFactorization tb) :=
      (Finite.injective_iff_surjective_of_equiv e.symm).2 Set.rangeFactorization_surjective
    exact fun a b hab => hr (Subtype.ext hab)

  have hsf : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).Finite :=
    (Set.finite_range tb).preimage Subtype.val_injective.injOn
  have hle : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).ncard ≤ t.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Cardinal.toNat_le_toNat ((h2.trans h3).trans hσt) (hsf.subset hts).lt_aleph0
  rw [Set.eq_of_subset_of_ncard_le hts hle hsf] at hb
  let g : σ → Algebra.adjoin E (Set.range tb) := fun i => ⟨tb i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hrange : Set.range g = ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hg : AlgebraicIndependent E g := by
    rw [← algebraicIndependent_subtype_range hginj, hrange]
    exact hb.1
  exact hg.map' (f := (Algebra.adjoin E (Set.range tb)).val) Subtype.val_injective

theorem gauss_card_arith {a b : Cardinal} {s d : ℕ} (h : ((s + d : ℕ) : Cardinal) ≤ a + b)
    (ha : a ≤ d) (hb : b ≤ s) : a = d ∧ b = s := by
  obtain ⟨a', rfl⟩ := Cardinal.lt_aleph0.1 (ha.trans_lt Cardinal.natCast_lt_aleph0)
  obtain ⟨b', rfl⟩ := Cardinal.lt_aleph0.1 (hb.trans_lt Cardinal.natCast_lt_aleph0)
  have h' : s + d ≤ a' + b' := by exact_mod_cast h
  have ha' : a' ≤ d := by exact_mod_cast ha
  have hb' : b' ≤ s := by exact_mod_cast hb
  constructor
  · exact_mod_cast (by omega : a' = d)
  · exact_mod_cast (by omega : b' = s)

theorem gauss_aeval_mem {B C : Type} [CommRing B] [CommRing C] [Algebra B C] {σ : Type}
    (g : σ → C) (P : MvPolynomial σ B) (R : Subring C)
    (hc : ∀ α, algebraMap B C (P.coeff α) ∈ R) (hg : ∀ s, g s ∈ R) : aeval g P ∈ R := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  exact R.sum_mem fun α _ => R.mul_mem (hc α) (R.prod_mem fun i _ => R.pow_mem (hg i) _)

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.LogNormEvalZeroLeCircleAverage
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem log_norm_eval_zero_le_circleAverage (q : ℂ[X]) (hq : q.eval 0 ≠ 0) :
    Real.log ‖q.eval 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖q.eval ζ‖) 0 1 := by
  have hA : AnalyticOnNhd ℂ (fun z => q.eval z) Set.univ := fun z _ =>
    (Polynomial.differentiable q).analyticAt z
  have hM : MeromorphicOn (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    (hA.mono (Set.subset_univ _)).meromorphicOn
  have hD : 0 ≤ MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hA.mono (Set.subset_univ _))
  rw [MeromorphicOn.circleAverage_log_norm one_ne_zero hM,
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (hA 0 trivial) hq, Real.log_one, mul_zero,
    add_zero]
  have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor (fun z => q.eval z)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) * Real.log (1 * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)|
    · have hle : ‖u‖ ≤ 1 := by simpa using hu
      apply mul_nonneg
      · exact_mod_cast (show (0 : ℤ) ≤ _ by simpa using hD u)
      · rw [one_mul, Real.log_inv, zero_sub, norm_neg]
        exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hle)
    · have h0 : MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u = 0 := by
        by_contra h
        exact hu (Function.locallyFinsuppWithin.supportWithinDomain _ (Function.mem_support.mpr h))
      simp [h0]
  linarith

theorem eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ ℂ} {a : ℕ}
    (hf : f.IsHomogeneous a) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ a * MvPolynomial.eval x f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = a := by
    have h := hf (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiContractA
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨N, hN⟩ : ∃ N : Matrix (k ⊕ m) m ℂ, N = fromRows (-(A⁻¹ * B)) 1 := ⟨_, rfl⟩
  have hinj : Function.Injective N.mulVec := by
    intro v w hvw
    funext i
    have h1 := congrFun hvw (Sum.inr i)
    simpa [hN, fromRows_mulVec] using h1
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  have h1 : A * (-(A⁻¹ * B)) + B * (1 : Matrix m m ℂ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have h2 : Bᴴ * (-(A⁻¹ * B)) + D * (1 : Matrix m m ℂ) = D - Bᴴ * A⁻¹ * B := by
    rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  have key : Nᴴ * fromBlocks A B Bᴴ D * N = D - Bᴴ * A⁻¹ * B := by
    rw [hN, conjTranspose_fromRows_eq_fromCols_conjTranspose, ← fromRows_fromCols_eq_fromBlocks,
      fromCols_mul_fromRows, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [fromCols_mul_fromRows, fromCols_mul_fromRows, h1, h2, Matrix.mul_zero, zero_add,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpd := h.conjTranspose_mul_mul_same hinj
  rwa [key] at hpd

end ReciprocityTheory.MultiplicativeHeights
end

