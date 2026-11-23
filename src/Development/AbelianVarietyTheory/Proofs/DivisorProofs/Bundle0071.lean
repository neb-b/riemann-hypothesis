module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtale
section
namespace GlobalTheory.EtaleIsolate

theorem primes_above_finite {A : Type*} [CommRing A] (I : Ideal A) [IsArtinianRing (A ⧸ I)] :
    {Q : Ideal A | Q.IsPrime ∧ I ≤ Q}.Finite ∧
      ∀ Q : Ideal A, Q.IsPrime → I ≤ Q → Q.IsMaximal := by
  have key : ∀ Q : Ideal A, Q.IsPrime → I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).IsPrime ∧
        (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hQ hIQ
    have hk : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rwa [Ideal.mk_ker]
    refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hk, ?_⟩
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIQ]
  refine ⟨((IsArtinianRing.setOfPred_isPrime_finite (A ⧸ I)).image
    (Ideal.comap (Ideal.Quotient.mk I))).subset fun Q hQ => ?_, fun Q hQ hIQ => ?_⟩
  · exact ⟨_, (key Q hQ.1 hQ.2).1, (key Q hQ.1 hQ.2).2⟩
  · haveI := (key Q hQ hIQ).1
    have hm := IsArtinianRing.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk I))
    rw [← (key Q hQ hIQ).2]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot_span (B : Type*) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : IsArtinianRing (B ⧸ Ideal.span {f}) := by
  have hr0 : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  haveI : IsArtinian B (B ⧸ Ideal.span {f}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton B hr0)).2
  exact isArtinian_of_tower B inferInstance

theorem isArtinianRing_fibre (B D : Type*) [CommRing B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (P : Ideal B) [P.IsMaximal] :
    IsArtinianRing (D ⧸ P.map (algebraMap B D)) := by
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.Etale (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D P).symm
  haveI : Module.Finite (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  exact IsArtinianRing.of_finite (B ⧸ P) _

theorem exists_isolating (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D]
    [Algebra B D] [Algebra.Etale B D] (f : B) (hf : f ≠ 0) (Q : Ideal D) (hQ : Q.IsMaximal) :
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  classical
  haveI := isArtinianRing_quot_span B f hf
  obtain ⟨hBfin, hBmax⟩ := primes_above_finite (Ideal.span {f})
  set S : Set (Ideal D) := {Q' | Q'.IsPrime ∧ algebraMap B D f ∈ Q'} with hS
  set T : Set (Ideal B) := {P | P.IsPrime ∧ Ideal.span {f} ≤ P} with hT
  have hsub : S ⊆ ⋃ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'} := by
    rintro Q' ⟨hQ', hfQ'⟩
    refine Set.mem_biUnion (x := Q'.comap (algebraMap B D)) ⟨Ideal.IsPrime.comap _, ?_⟩
      ⟨hQ', Ideal.map_comap_le⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hfQ'
  have hfib : ∀ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'}.Finite ∧
      ∀ Q' : Ideal D, Q'.IsPrime → P.map (algebraMap B D) ≤ Q' → Q'.IsMaximal := by
    rintro P ⟨hP, hfP⟩
    haveI := hBmax P hP hfP
    haveI := isArtinianRing_fibre B D P
    exact primes_above_finite _
  have hSfin : S.Finite := (hBfin.biUnion fun P hP => (hfib P hP).1).subset hsub
  have hSmax : ∀ Q' ∈ S, Q'.IsMaximal := fun Q' hQ' => by
    obtain ⟨P, hP, hQ'P⟩ := Set.mem_iUnion₂.mp (hsub hQ')
    exact (hfib P hP).2 Q' hQ'P.1 hQ'P.2
  have hch : ∀ Q' ∈ S, Q' ≠ Q → ∃ x, x ∈ Q' ∧ x ∉ Q := fun Q' hQ' hne => by
    by_contra h
    push_neg at h
    exact hne ((hSmax Q' hQ').eq_of_le hQ.ne_top h)
  choose! x hxmem hxnot using hch
  refine ⟨∏ Q' ∈ hSfin.toFinset.filter (· ≠ Q), x Q', ?_, ?_⟩
  · intro h
    haveI := hQ.isPrime
    obtain ⟨Q', hQ', hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hQ'
    exact hxnot Q' hQ'.1 hQ'.2 hmem
  · intro Q' hQ' hfQ' hg
    by_contra hne
    apply hg
    have hmem : Q' ∈ hSfin.toFinset.filter (· ≠ Q) :=
      Finset.mem_filter.2 ⟨hSfin.mem_toFinset.2 ⟨hQ', hfQ'⟩, hne⟩
    rw [← Finset.prod_erase_mul _ _ hmem]
    exact Ideal.mul_mem_left _ _ (hxmem Q' ⟨hQ', hfQ'⟩ hne)

theorem isolate_maximal_among_primes_containing : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal →
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q :=
  fun B D _ _ _ _ _ f hf Q hQ => exists_isolating B D f hf Q hQ

end GlobalTheory.EtaleIsolate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetsMemSubalgebraOfFiniteType
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem jets_mem_subalgebra_of_finiteType : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  intro k A R _ _ _ _ _ _ N Δ _ hL
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨(Finset.range N ×ˢ insert 1 s).image (fun x => Δ x.1 x.2), ?_⟩
  intro S hT l hl u
  have key : ∀ u ∈ Algebra.adjoin k (s : Set A), ∀ l < N, Δ l u ∈ S := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      intro l hl
      exact hT _ (Finset.mem_image.2 ⟨(l, x), by simp [hl, Finset.mem_coe.1 hx], rfl⟩)
    | algebraMap c =>
      intro l hl
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact S.smul_mem (hT _ (Finset.mem_image.2 ⟨(l, 1), by simp [hl], rfl⟩)) c
    | add x y _ _ hx hy =>
      intro l hl
      rw [map_add (f := _)]
      exact S.add_mem (hx l hl) (hy l hl)
    | mul x y _ _ hx hy =>
      intro l hl
      rw [hL]
      refine S.sum_mem (fun p hp => S.mul_mem (hx p ?_) (hy (l - p) ?_))
      · have := Finset.mem_range.1 hp; omega
      · omega
  exact key u (hs ▸ Algebra.mem_top) l hl

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointCoverSectionDetectRestrictOpen
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

lemma resLE_self_preimage_image_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens)
    (W : V.toScheme.Opens) :
    (e₁ ⁻¹ᵁ V).ι ''ᵁ ((e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl) ⁻¹ᵁ W) = e₁ ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr (fun x hx => V.ι_image_le W hx)

lemma resLE_self_app_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens) (W : V.toScheme.Opens)
    (a b : Γ(V.toScheme, W))
    (h : (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b) :
    e₁.app (V.ι ''ᵁ W) a = e₁.app (V.ι ''ᵁ W) b := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE] at h
  have hS := resLE_self_preimage_image_eq e₁ V W
  have key := Scheme.Hom.appLE_map' (f := e₁) (U := V.ι ''ᵁ W)
    (e := le_refl (e₁ ⁻¹ᵁ (V.ι ''ᵁ W))) (i := hS.symm)
  rw [Scheme.Hom.appLE_eq_app] at key
  rw [← key]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ h

theorem cover_and_joint_inj_restrict : ∀ (Z Z₁ Z₂ : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z),
    (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) →
    (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) →
    ∀ V : Z.Opens, (∀ z : V.toScheme, (∃ z₁, e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl z₁ = z) ∨
      ∃ z₂, e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl z₂ = z) ∧
    ∀ (W : V.toScheme.Opens) (a b : Γ(V.toScheme, W)),
      (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b →
      (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W a = (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W b → a = b := by
  intro Z Z₁ Z₂ e₁ e₂ hcov hinj V
  refine ⟨fun z => ?_, fun W a b h₁ h₂ =>
    hinj _ a b (resLE_self_app_eq e₁ V W a b h₁) (resLE_self_app_eq e₂ V W a b h₂)⟩
  rcases hcov z.1 with ⟨z₁, hz⟩ | ⟨z₂, hz⟩
  · refine Or.inl ⟨⟨z₁, show e₁ z₁ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz
  · refine Or.inr ⟨⟨z₂, show e₂ z₂ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalOrthogonalRangeUnitarySelfReciprocal
section
open Matrix Polynomial

namespace GlobalTheory

theorem csr_transpose_aeval {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p)ᵀ = aeval Aᵀ p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [transpose_smul, transpose_pow]

theorem csr_map_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p).map σ = aeval (A.map σ) (p.map σ) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := p.natDegree + 1)]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingHom.mapMatrix_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow : (A ^ i).map σ = (A.map σ) ^ i := by
      rw [← RingHom.mapMatrix_apply, map_pow]; rfl
    rw [coeff_map, RingHom.mapMatrix_apply, ← hpow]
    ext a b
    simp [Matrix.smul_apply]
  · exact Nat.lt_succ_of_le (natDegree_map_le)

theorem csr_pow_mul_pow {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (d i : ℕ) (hi : i ≤ d) : γ ^ d * B ^ i = γ ^ (d - i) := by
  have key : ∀ j, γ ^ j * B ^ j = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc γ, h, one_mul, ih]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_comm i e, pow_add, mul_assoc, key, mul_one, Nat.add_sub_cancel]

theorem csr_reverse {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (P : K[X]) :
    γ ^ P.natDegree * aeval B P = aeval γ P.reverse := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := P.natDegree + 1), Finset.mul_sum]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : P.natDegree + 1 - 1 - i = P.natDegree - i := by omega
    rw [e1, mul_smul_comm, csr_pow_mul_pow γ B h _ _ (Nat.sub_le _ _), coeff_reverse,
      revAt_le hi']
    have e2 : P.natDegree - (P.natDegree - i) = i := by omega
    rw [e2]
  · exact Nat.lt_succ_of_le (reverse_natDegree_le P)

end GlobalTheory

namespace GlobalTheory

theorem csr_ker_orth_range {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K)
    (hx : aeval γ Q *ᵥ x = 0) : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  have hγB : γ * (γ.map σ)ᵀ = 1 := mul_eq_one_comm.mp hγ
  have hMt : ((aeval γ Q).map σ)ᵀ = aeval (γ.map σ)ᵀ (Q.map σ) := by
    rw [csr_map_aeval, csr_transpose_aeval]
  have hrev : aeval γ (Q.map σ).reverse = σ (Q.coeff 0) • aeval γ Q := by
    rw [← hQ, aeval_mul, aeval_C, Algebra.smul_def]
  have hBd : (γ.map σ)ᵀ ^ (Q.map σ).natDegree * γ ^ (Q.map σ).natDegree = 1 := by
    rw [csr_pow_mul_pow _ _ hγ _ _ le_rfl, Nat.sub_self, pow_zero]
  have hBP : aeval (γ.map σ)ᵀ (Q.map σ)
      = (γ.map σ)ᵀ ^ (Q.map σ).natDegree * (σ (Q.coeff 0) • aeval γ Q) := by
    rw [← hrev, ← csr_reverse γ _ hγB, ← mul_assoc, hBd, one_mul]
  have hBx : aeval (γ.map σ)ᵀ (Q.map σ) *ᵥ x = 0 := by
    rw [hBP, ← mulVec_mulVec, smul_mulVec, hx, smul_zero, mulVec_zero]
  have expand : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k
      = ∑ l, σ (z l) * ((((aeval γ Q).map σ)ᵀ) *ᵥ x) l := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      transpose_apply, map_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [expand, hMt, hBx]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentation
section
open scoped TensorProduct

namespace GlobalTheory

theorem ker_aeval_truncated : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  intro n hn B A _ _ _ d x b hx hli
  set J : Ideal (MvPolynomial (Fin d) B) := Ideal.span (Set.range fun i : Fin d =>
    (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) with hJ
  have hJker : J ≤ RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, hx]
  refine le_antisymm ?_ hJker
  let q : MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin d) B ⧸ J) := Ideal.Quotient.mkₐ B J
  have hq : ∀ F G, q F = q G ↔ F - G ∈ J := fun F G => by
    simp only [q, Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq
  let y : Fin d → (MvPolynomial (Fin d) B ⧸ J) := fun i => q (MvPolynomial.X i)
  let v : (Fin d → Fin n) → (MvPolynomial (Fin d) B ⧸ J) := fun a => ∏ i, y i ^ (a i : ℕ)
  have hqv : ∀ a, q (∏ i, MvPolynomial.X i ^ (a i : ℕ)) = v a := fun a => by
    simp [v, y, map_prod, map_pow]
  have hyn : ∀ i, y i ^ n = algebraMap B _ (b i) := by
    intro i
    have h1 : q (MvPolynomial.X i ^ n) = q (MvPolynomial.C (b i)) :=
      (hq _ _).mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp only [y]
    rw [← map_pow, h1, ← MvPolynomial.algebraMap_eq, q.commutes]
  have hsplit : ∀ (a : Fin d → Fin n) (i : Fin d) (k : Fin n),
      v (Function.update a i k) = y i ^ (k : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i k
    simp only [v]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have hsplit0 : ∀ (a : Fin d → Fin n) (i : Fin d),
      v a = y i ^ (a i : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i
    have := hsplit a i (a i)
    rwa [Function.update_eq_self] at this
  let S := Submodule.span B (Set.range v)
  have hgen : ∀ (a : Fin d → Fin n) (i : Fin d), v a * y i ∈ S := by
    intro a i
    by_cases h : (a i : ℕ) + 1 < n
    · have : v a * y i = v (Function.update a i ⟨a i + 1, h⟩) := by
        rw [hsplit, hsplit0 a i, pow_succ]; ring
      rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
    · have h' : (a i : ℕ) + 1 = n := by have := (a i).isLt; omega
      have : v a * y i = b i • v (Function.update a i ⟨0, hn⟩) := by
        have hp : y i ^ n = y i ^ ((a i : ℕ) + 1) := by rw [h']
        rw [hsplit, hsplit0 a i, Algebra.smul_def, ← hyn, hp, pow_succ]; simp; ring
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hmulX : ∀ i, ∀ s ∈ S, s * y i ∈ S := by
    intro i s hs
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨a, rfl⟩ := hs; exact hgen a i
    | zero => simp
    | add s t _ _ hs ht => rw [add_mul]; exact add_mem hs ht
    | smul c s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hs
  have hall : ∀ F, q F ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : q (MvPolynomial.C c) = c • v (fun _ => ⟨0, hn⟩) := by
        rw [← MvPolynomial.algebraMap_eq, q.commutes, Algebra.algebraMap_eq_smul_one]
        simp [v]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp => rw [map_mul]; exact hmulX i _ hp
  intro F hF
  rw [RingHom.mem_ker] at hF
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp (hall F)
  set G : MvPolynomial (Fin d) B := ∑ a, c a • ∏ i, MvPolynomial.X i ^ (a i : ℕ) with hG
  have hqG : q G = q F := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hqv]
  have hFG : F - G ∈ J := (hq F G).mp hqG.symm
  have hevG : MvPolynomial.aeval x G = 0 := by
    have h0 := hJker hFG
    rw [RingHom.mem_ker, map_sub, hF] at h0
    simpa using h0
  have hsum : ∑ a, c a • ∏ i, x i ^ (a i : ℕ) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hevG, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by simp [map_prod, map_pow]
  have hc0 := Fintype.linearIndependent_iff.mp hli c hsum
  have hG0 : G = 0 := by rw [hG]; simp [hc0]
  simpa [hG0] using hFG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerCounitAlgHomBaseChangeField
section
open TensorProduct

namespace GlobalTheory

theorem ker_counitAlgHom_baseChange_field (O B κ : Type) [CommRing O] [CommRing B] [Bialgebra O B]
    [Field κ] [Algebra O κ] :
    RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)) =
      Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B)
        (RingHom.ker (Bialgebra.counitAlgHom O B)) := by
  have hs : Function.Surjective (Bialgebra.counitAlgHom O B) := fun c =>
    ⟨algebraMap O B c, by simp⟩
  rw [← Algebra.TensorProduct.lTensor_ker _ hs]
  have key : ∀ x : κ ⊗[O] B, Bialgebra.counitAlgHom κ (κ ⊗[O] B) x =
      Algebra.TensorProduct.rid O κ κ
        (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O B) x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c b => simp [TensorProduct.counit_tmul]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, key, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem hopf_order_formula_fibre :
    (∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Module.finrank k A = Module.finrank k (A ⧸ Ideal.map (f : B →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k B))) * Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap)) → ∀ (O A B κ : Type) [CommRing O] [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B] [Module.Finite O A] [Field κ] [Algebra O κ] (f : B →ₐc[O] A), Module.finrank κ (TensorProduct O κ A) = Module.finrank κ (TensorProduct O κ (A ⧸ Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))) * Module.finrank κ (LinearMap.range ((f : B →ₐ[O] A).toLinearMap.baseChange κ)) := by
  intro H O A B κ _ _ _ _ _ _ _ _ f
  have h := H κ (κ ⊗[O] A) (κ ⊗[O] B) (Bialgebra.TensorProduct.map (BialgHom.id κ κ) f)
  have hI : Ideal.map ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B))) =
      Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A)
        (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B))) := by
    rw [ker_counitAlgHom_baseChange_field]
    refine (Ideal.map_map
      ((Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) : B →+* κ ⊗[O] B)
      ((((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)) : κ ⊗[O] B →+* κ ⊗[O] A)).trans ?_
    refine Eq.trans ?_ (Ideal.map_map ((f : B →ₐ[O] A) : B →+* A)
      ((Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) : A →+* κ ⊗[O] A)).symm
    congr 1
  have hL : ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A).toLinearMap =
      (f : B →ₐ[O] A).toLinearMap.baseChange κ := by
    ext b
    simp
  rw [hI, hL] at h
  rw [h, (Algebra.TensorProduct.tensorQuotientEquiv (R := O) κ A κ
    (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))).toLinearEquiv.finrank_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTarget
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_fin_sum_of_mem_ideal_smul_top {B P : Type} [CommRing B] [AddCommGroup P]
    [Module B P] (I : Ideal B) {z : P} (hz : z ∈ I • (⊤ : Submodule B P)) :
    ∃ (n : ℕ) (b : Fin n → B) (p : Fin n → P), (∀ i, b i ∈ I) ∧ ∑ i, b i • p i = z := by
  refine Submodule.smul_induction_on hz
    (fun r hr m _ => ⟨1, fun _ => r, fun _ => m, fun _ => hr, by simp⟩) ?_
  rintro x y ⟨n, b, p, hb, rfl⟩ ⟨n', b', p', hb', rfl⟩
  refine ⟨n + n', Fin.append b b', Fin.append p p', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hb, hb']
  · simp [Fin.sum_univ_add]

theorem ker_inf_map_le_map_mul_ker_of_flat :
    ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A]
      [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B,
      RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  intro B P A _ _ _ _ _ _ Ψ hΨ I z hz
  have hz1 : Ψ z = 0 := RingHom.mem_ker.1 hz.1
  have hz2 : z ∈ I • (⊤ : Submodule B P) := by
    rw [Ideal.smul_top_eq_map]; exact hz.2
  obtain ⟨n, b, p, hb, rfl⟩ := exists_fin_sum_of_mem_ideal_smul_top I hz2
  have h0 : ∑ i, b i • Ψ (p i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul] using hz1
  obtain ⟨k, c, a, hx, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := A)
    (f := b) (x := fun i => Ψ (p i)) h0
  choose q hq using fun j => hΨ (a j)
  have hzero : ∑ i, ∑ j, (b i * c i j) • q j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, hc j, zero_smul]
  have key : ∑ i, b i • p i = ∑ i, b i • (p i - ∑ j, c i j • q j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hzero, sub_zero]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hb i)) ?_
  rw [RingHom.mem_ker]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, hq, ← hx i, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LtNatCastOfAddOneLtSucc
section
namespace GlobalTheory.NatCastStrictBound

theorem lt_natCast_of_add_one_lt_succ :
    ∀ {a : WithBot ℕ∞} {n : ℕ}, a + (1 : WithBot ℕ∞) < (↑(n + (1 : ℕ)) : WithBot ℕ∞) →
      a < (↑n : WithBot ℕ∞) := by
  intro a n h
  by_contra hc
  have hle : (↑n : WithBot ℕ∞) ≤ a := not_lt.mp hc
  have h2 : (↑n : WithBot ℕ∞) + 1 ≤ a + 1 := by gcongr
  rw [Nat.cast_add, Nat.cast_one] at h
  exact absurd h (not_lt.mpr h2)

end GlobalTheory.NatCastStrictBound
end

