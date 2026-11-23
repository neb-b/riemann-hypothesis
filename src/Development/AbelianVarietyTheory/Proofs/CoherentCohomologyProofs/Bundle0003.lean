module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal
section
open IsLocalRing TensorProduct

namespace GlobalTheory

section Local

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

theorem nonempty_baseChange_subquotient_equiv [Module.Flat R S] {X : Type*} [AddCommGroup X]
    [Module R X] (A B : Submodule R X) :
    Nonempty ((S ⊗[R] (A ⧸ B.submoduleOf A)) ≃ₗ[S]
      (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S))) := by
  let h : S ⊗[R] A →ₗ[S] S ⊗[R] (A ⧸ B.submoduleOf A) := (B.submoduleOf A).mkQ.baseChange S
  let g : S ⊗[R] A →ₗ[S] (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) :=
    ((B.baseChange S).submoduleOf (A.baseChange S)).mkQ ∘ₗ A.toBaseChange S
  have hh : Function.Surjective h :=
    LinearMap.lTensor_surjective S (B.submoduleOf A).mkQ_surjective
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (A.toBaseChange_surjective S)
  have e₁ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.submoduleOf A).mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have e₂ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.mkQ ∘ₗ A.subtype).lTensor S) := by
    apply Module.Flat.lTensor_exact S
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
    rfl
  have e₃ : Function.Exact (B.subtype.lTensor S) (B.mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have hker : LinearMap.ker h = LinearMap.ker g := by
    ext x
    have h1 : x ∈ LinearMap.ker h ↔ (B.submoduleOf A).mkQ.lTensor S x = 0 := Iff.rfl
    have h2 : x ∈ LinearMap.ker g ↔ A.subtype.lTensor S x ∈ B.baseChange S := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h1, h2, e₁ x, ← e₂ x, LinearMap.lTensor_comp, LinearMap.comp_apply, e₃]
    rfl
  exact ⟨(h.quotKerEquivOfSurjective hh).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    g.quotKerEquivOfSurjective hg⟩

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_flat :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  IsLocalRing.length_baseChange R S X


variable {X} in
theorem length_baseChange_subquotient_flat (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) *
        Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  rw [← length_baseChange_flat]
  exact (nonempty_baseChange_subquotient_equiv R S A B).some.length_eq.symm

variable {R S}

end Local

section DVR

open IsDiscreteValuationRing hiding maximalIdeal

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

theorem length_quotient_span_singleton_eq_addVal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addVal_zero, Ideal.span_singleton_zero,
      (Submodule.quotEquivOfEqBot (⊥ : Ideal S) rfl).length_eq]
    by_contra h
    have h' := Module.length_ne_top_iff.mp h
    rw [← isArtinianRing_iff_isFiniteLength] at h'
    exact not_isField S (IsArtinianRing.isField_of_isDomain S)
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal]

variable [IsLocalHom (algebraMap R S)]

theorem map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpS : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hpS hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S) hp,
    Ideal.ramificationIdx'_spec (n := n) hn.le, hn]
  rw [hn]
  exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) n).not_ge

theorem length_fibre_eq_ramificationIdx :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by
  conv_lhs => rw [map_maximalIdeal_eq_pow_ramificationIdx]
  exact length_quotient_pow_maximalIdeal S _

theorem ramificationIdx_maximalIdeal_pos : 0 < (maximalIdeal S).ramificationIdx R := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := map_maximalIdeal_eq_pow_ramificationIdx R S
  rw [h, pow_zero, Ideal.one_eq_top] at this
  exact (map_maximalIdeal_lt_top (algebraMap R S)).ne this


variable {R} in
theorem addVal_algebraMap_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [← length_fibre_eq_ramificationIdx, ← length_quotient_span_singleton_eq_addVal,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]


variable {R} in
theorem addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul]
    exact_mod_cast (ramificationIdx_maximalIdeal_pos R S).ne'
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
    rw [addVal_def' u hϖ, map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_algebraMap_uniformizer S hϖ,
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, nsmul_eq_mul]

variable (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_dvr :
    Module.length S (S ⊗[R] X) =
      Module.length R X * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_flat, length_fibre_eq_ramificationIdx]


variable {X} in
theorem length_baseChange_subquotient_dvr (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_subquotient_flat, length_fibre_eq_ramificationIdx]

end DVR

section Uniformizer

open IsDiscreteValuationRing hiding maximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

end Uniformizer

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthEqTopOfFinrankNeZero
section
universe u_1 u_2

namespace GlobalTheory.LengthCokernelFinrank

open Module Submodule IsDiscreteValuationRing

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h0 : Module.length R (R ⧸ Ideal.span {(0 : R)}) = ⊤ := by
    have h := Ring.ord_eq_addVal (0 : R)
    rw [addVal_zero] at h
    exact h
  have hle := Module.length_le_of_surjective (Submodule.mkQ (Ideal.span {(0 : R)}))
    (Submodule.mkQ_surjective _)
  rw [h0] at hle
  exact top_le_iff.mp hle

theorem addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

variable {M : Type u_2} [AddCommGroup M] [Module R M]

theorem length_eq_top_of_finrank_ne_zero [Module.Finite R M] (h : finrank R M ≠ 0) :
    Module.length R M = ⊤ := by
  have hnt : ¬ Module.IsTorsion R M := fun ht => h (Module.finrank_eq_zero_iff_isTorsion.mpr ht)
  have hx : ∃ x : M, ∀ a : R, a • x = 0 → a = 0 := by
    by_contra hc
    push Not at hc
    apply hnt
    intro x
    obtain ⟨a, ha, ha0⟩ := hc x
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, ha⟩
  obtain ⟨x, hx⟩ := hx
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M x) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hx a (by simpa using ha)
  have hle := Module.length_le_of_injective _ hinj
  rw [length_self_eq_top] at hle
  exact top_le_iff.mp hle

theorem length_coker_eq_addVal_det [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  classical
  by_cases hk : LinearMap.ker f = ⊥
  · have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hk
    set N := LinearMap.range f with hN
    let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
    let b := Module.Free.chooseBasis R M
    have h : finrank R N = finrank R M := e.symm.finrank_eq
    let a := smithNormalFormCoeffs b h
    let b' := smithNormalFormTopBasis b h
    let ab := smithNormalFormBotBasis b h
    let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
    let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
    have hf : f = N.subtype ∘ₗ (e : M →ₗ[R] N) := by
      ext x
      rfl
    have hassoc : Associated (LinearMap.det f) (LinearMap.det g) := by
      have := LinearMap.associated_det_comp_equiv N.subtype e e'
      rwa [← hf] at this
    have hg : ∀ i, g (b' i) = a i • b' i := by
      intro i
      have : e' (b' i) = ab i := by simp [e']
      change ((e' (b' i) : N) : M) = _
      rw [this]
      exact smithNormalFormBotBasis_def b h i
    have hmat : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one, Matrix.diagonal_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have hdet : LinearMap.det g = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal]
    rw [(addVal_eq_iff_associated _ _).mpr hassoc, hdet, addVal_prod,
      (quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
  · rw [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk, addVal_zero]
    apply length_eq_top_of_finrank_ne_zero
    intro h0
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
    rw [(LinearMap.quotKerEquivRange f).finrank_eq] at h2
    have h3 : finrank R (LinearMap.ker f) = 0 := by omega
    exact hk (Submodule.finrank_eq_zero.mp h3)

end GlobalTheory.LengthCokernelFinrank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientSpanSingleton
section
universe u_1 u_2

namespace GlobalTheory.LengthQuotientValuationDet

open Module IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

theorem length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

theorem length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end GlobalTheory.LengthQuotientValuationDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthSelfEqTop
section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.LengthQuotientSpanValuation

open Module

section

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma length_quot_span (x : R) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x :=
  Ring.ord_eq_addVal x

lemma length_self_eq_top : Module.length R R = ⊤ := by
  rw [← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

end

theorem main {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by
  set A := LinearMap.toMatrix b' b f with hA
  by_cases hf : Function.Injective f
  · set N := LinearMap.range f with hN
    let e₀ : M' ≃ₗ[R] N := LinearEquiv.ofInjective f hf
    have h : Module.finrank R N = Module.finrank R M := by
      rw [← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
    let a := Submodule.smithNormalFormCoeffs b h
    let bT := Submodule.smithNormalFormTopBasis b h
    let bB := Submodule.smithNormalFormBotBasis b h
    have ab_eq := Submodule.smithNormalFormBotBasis_def b h

    have hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i) := by
      rw [(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype,
        addVal_prod]
      exact Finset.sum_congr rfl fun i _ => length_quot_span _
    rw [hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]

    let φ : M' ≃ₗ[R] M := b'.equiv b (Equiv.refl ι)
    have hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N)) := by
      rw [← LinearMap.det_toMatrix b]
      congr 1
      ext i j
      simp [hA, LinearMap.toMatrix_apply, φ, e₀]
      rfl
    let e' : M ≃ₗ[R] N := bT.equiv bB (Equiv.refl ι)
    have hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i := by
      intro i
      simp [e', Basis.equiv_apply, bB, bT, a, ab_eq]
    have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hdetA, ← hdiag]
    exact LinearMap.associated_det_comp_equiv _ _ _
  · have hdet : A.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
        simpa [Function.Injective] using hf
      refine ⟨b'.repr (x - y), ?_, ?_⟩
      · intro h
        apply hne
        rw [← sub_eq_zero]
        apply b'.repr.injective
        rw [map_zero]
        exact Finsupp.ext fun i => by simpa using congrFun h i
      · rw [hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
        rfl
    rw [hdet, IsDiscreteValuationRing.addVal_zero]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    let φ : M →ₗ[R] R := ∑ i, w i • b.coord i
    have hφ : ∀ x, φ x = ∑ i, w i * b.repr x i := by
      intro x
      simp [φ]
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rw [LinearMap.range_le_ker_iff]
      refine b'.ext fun j => ?_
      have := congrFun hw j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    let ψ := (LinearMap.range f).liftQ φ hle
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    have hmem : (R ∙ w i) ≤ LinearMap.range ψ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨Submodule.Quotient.mk (b i), ?_⟩
      simp [ψ, hφ, Finsupp.single_apply]
    have h1 : Module.length R (R ∙ w i) = ⊤ := by
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]
    have h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ) :=
      Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)
    have h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f) :=
      Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
    rw [← top_le_iff, ← h1]
    exact h2.trans h3

end GlobalTheory.LengthQuotientSpanValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemSaturationOfPowSmulMem
section
namespace GlobalTheory.SubmoduleSaturation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

def saturation (g : A) (K : Submodule A M) : Submodule A M where
  carrier := {m | ∃ k : ℕ, g ^ k • m ∈ K}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [smul_add]
    refine K.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hk
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hl
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact K.smul_mem _ hk

end GlobalTheory.SubmoduleSaturation
end

