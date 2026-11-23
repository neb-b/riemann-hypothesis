module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bounds
section
namespace KStar.Ram

open DirichletCharacter

section PrimePower

variable {l v : ℕ} [hl : Fact l.Prime]

private instance bounds_neZero : NeZero (l ^ v) := ⟨pow_ne_zero _ hl.out.ne_zero⟩

end PrimePower

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycDifferent
section
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

open Polynomial in
private theorem minpoly_map_eq_prod_gal {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (x : L) (hx : Algebra.adjoin F {x} = ⊤) :
    (minpoly F x).map (algebraMap F L) = ∏ σ : Gal(L/F), (X - C (σ x)) := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hinj : Function.Injective (fun σ : Gal(L/F) => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hx
    rintro y rfl
    exact h
  have hm : (∏ σ : Gal(L/F), (X - C (σ x))).Monic :=
    monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C _
  have hdvd : (∏ σ : Gal(L/F), (X - C (σ x))) ∣ (minpoly F x).map (algebraMap F L) := by
    apply Finset.prod_dvd_of_coprime
    · intro σ _ τ _ hne
      exact pairwise_coprime_X_sub_C hinj hne
    · intro σ _
      rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, aeval_algEquiv]
      simp
  refine eq_of_monic_of_dvd_of_natDegree_le hm ((minpoly.monic hint).map _) hdvd ?_
  rw [natDegree_map, natDegree_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact minpoly.natDegree_le x

open Polynomial Classical in
private theorem aeval_derivative_minpoly_eq_prod_gal {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (x : L)
    (hx : Algebra.adjoin F {x} = ⊤) :
    aeval x (derivative (minpoly F x)) = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1, (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, minpoly_map_eq_prod_gal x hx,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Gal(L/F))), derivative_mul]
  simp [eval_prod]

open Polynomial Classical in
private theorem differentIdeal_eq_span_of_prod (A F : Type*) {L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [NumberField L] [Algebra A F] [IsFractionRing A F]
    [Algebra F L] [Algebra A L] [Algebra A (𝓞 L)] [IsScalarTower A F L] [IsScalarTower A (𝓞 L) L]
    [IsIntegralClosure (𝓞 L) A L] [Module.IsTorsionFree A (𝓞 L)]
    [FiniteDimensional F L] [IsGalois F L] (x y : 𝓞 L)
    (hx : Algebra.adjoin A {x} = ⊤) (hx' : Algebra.adjoin F {algebraMap (𝓞 L) L x} = ⊤)
    (hy : algebraMap (𝓞 L) L y = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1,
      (algebraMap (𝓞 L) L x - σ (algebraMap (𝓞 L) L x))) :
    differentIdeal A (𝓞 L) = Ideal.span {y} := by
  have h := conductor_mul_differentIdeal A F L x hx'
  rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul] at h
  rw [h]
  congr 2
  apply IsFractionRing.injective (𝓞 L) L
  have hint : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  rw [hy, ← aeval_derivative_minpoly_eq_prod_gal _ hx',
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint, derivative_map, aeval_map_algebraMap,
    aeval_algebraMap_apply]

private theorem adjoin_root_eq_top (E : Type*) [Field E] [Algebra ℚ E] [Algebra E K]
    [IsScalarTower ℚ E K] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin E {ζ} = ⊤ := by
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℚ {ζ} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℚ {ζ} ≤ (Algebra.adjoin E {ζ}).restrictScalars ℚ :=
    Algebra.adjoin_le (by simp)
  exact this hy

private theorem adjoin_toInteger_eq_top (A : Type*) [CommRing A] [Algebra A (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin A {hζ.toInteger} = ⊤ := by
  have h := adjoin_singleton_eq_top hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℤ {hζ.toInteger} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℤ {hζ.toInteger} ≤ (Algebra.adjoin A {hζ.toInteger}).restrictScalars ℤ :=
    Algebra.adjoin_le (by simp)
  exact this hy


open scoped Classical in
open Classical in
theorem relDifferent_eq_span_prod (E : IntermediateField ℚ K) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    differentIdeal (𝓞 E) (𝓞 K) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup ∧ σ ≠ 1),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  refine differentIdeal_eq_span_of_prod (𝓞 E) E hζ.toInteger _
    (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top E hζ) ?_
  rw [map_prod]
  symm
  refine Finset.prod_bij (fun σ _ => σ.restrictScalars ℚ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    · intro h
      apply (Finset.mem_erase.mp hσ).1
      ext x
      exact DFunLike.congr_fun h x
  · intro σ _ τ _ h
    ext x
    exact DFunLike.congr_fun h x
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨E.fixingSubgroupEquiv ⟨σ, hσ.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      apply hσ.2
      ext x
      exact DFunLike.congr_fun h x
    · rfl
  · intro σ _
    rfl


open scoped Classical in
open Classical in
theorem map_differentIdeal_eq_span_prod (E : IntermediateField ℚ K) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    (differentIdeal ℤ (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have h1 : differentIdeal ℤ (𝓞 K) = Ideal.span
      {∏ σ ∈ (Finset.univ : Finset Gal(K/ℚ)).erase 1, (hζ.toInteger - σ • hζ.toInteger)} := by
    refine differentIdeal_eq_span_of_prod ℤ ℚ hζ.toInteger _
      (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top ℚ hζ) ?_
    rw [map_prod]
    rfl
  have h2 := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 K)
  have h3 : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  apply mul_left_cancel₀ h3
  rw [← h2, h1, relDifferent_eq_span_prod E hζ, Ideal.span_singleton_mul_span_singleton,
    ← Finset.prod_filter_mul_prod_filter_not _ (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup)]
  congr 4
  · ext σ
    simp [and_comm]
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      and_iff_right_iff_imp]
    rintro h rfl
    exact h (one_mem _)

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
section
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem cycInertia_card_comap (l : ℕ) [hl : Fact l.Prime]
    (H : Subgroup (ZMod (ordCompl[l] N))ˣ) :
    Nat.card (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l))) =
      Nat.totient (ordProj[l] N) * Nat.card H := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have h1 := Subgroup.card_mul_index (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l)))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod (ordCompl[l] N))ˣ), ZMod.card_units_eq_totient] at h2
  have h3 : Nat.totient N = Nat.totient (ordProj[l] N) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))),
      Nat.ordProj_mul_ordCompl_eq_self]
  have h4 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4)
  rw [h1, h3, ← h2, mul_assoc]

private theorem cycInertia_ef (l : ℕ) [hl : Fact l.Prime] :
    (Ideal.span {(l : ℤ)}).ramificationIdxIn (𝓞 K) = Nat.totient (ordProj[l] N) ∧
      (Ideal.span {(l : ℤ)}).inertiaDegIn (𝓞 K) = orderOf (l : ZMod (ordCompl[l] N)) := by
  have h := (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  have hm : ¬ l ∣ ordCompl[l] N := Nat.not_dvd_ordCompl hl.out (NeZero.ne N)
  generalize ordCompl[l] N = m at h hm ⊢
  generalize N.factorization l = v at h ⊢
  cases v with
  | zero =>
    rw [pow_zero, one_mul] at h
    subst h
    exact ⟨by simpa using ramificationIdxIn_eq_of_not_dvd l K hm, inertiaDegIn_eq_of_not_dvd l K hm⟩
  | succ k =>
    exact ⟨by rw [ramificationIdxIn_eq N K h hm, Nat.totient_prime_pow_succ hl.out],
      inertiaDegIn_eq N K h hm⟩

private theorem cycInertia_key (l : ℕ) [hl : Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] (σ : Gal(K/ℚ)) (i : ℕ)
    (h : ∀ x : 𝓞 K, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ l ^ i) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (galEquivZMod N K σ) =
      ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)) ^ i := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have hζ := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger_isPrimitiveRoot
  have hη := hζ.pow (NeZero.pos N) (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  set η := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger ^ (ordProj[l] N)
  have h₀ : IsPrimitiveRoot (Ideal.Quotient.mk P η) (ordCompl[l] N) := by
    refine hη.idealQuotient_mk
      (by simpa using Ideal.IsPrime.ne_top inferInstance) ?_
    rw [← Ideal.pow_inertiaDeg l]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))
  have hi := h η
  rw [galEquivZMod_smul_of_pow_eq N _ _
    ((hη.pow_eq_one_iff_dvd _).mpr (Nat.ordCompl_dvd N l)), map_pow,
    (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
    ← h₀.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow] at hi
  ext
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← hi, ZMod.natCast_val]
  rfl

private theorem cycInertia_card_map (H : Subgroup Gal(K/ℚ)) :
    Nat.card (H.map (galEquivZMod N K).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (galEquivZMod N K).injective

theorem map_inertia_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (P.inertia Gal(K/ℚ)).map (galEquivZMod N K).toMonoidHom = inertiaUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    have := cycInertia_key (N := N) l P σ 0 (fun x => by
      rw [pow_zero, pow_one, Ideal.Quotient.eq]
      exact hσ x)
    rw [pow_zero] at this
    exact this
  · rw [cycInertia_card_map, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, inertiaUnits, ← MonoidHom.comap_bot, cycInertia_card_comap]
    simp


attribute [local instance] Ideal.Quotient.field in
theorem map_stabilizer_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (MulAction.stabilizer Gal(K/ℚ) P).map (galEquivZMod N K).toMonoidHom = decompUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(l : ℤ)})
    (by simpa using (Fact.out : l.Prime).ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
      (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩
    have : CharP (ℤ ⧸ Ideal.span {(l : ℤ)}) l := ringChar.of_eq <| Int.ringChar_idealQuot l
    have : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    obtain ⟨i, hi⟩ :=
      FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ Ideal.span {(l : ℤ)}) l (𝓞 K ⧸ P) τ
    have := cycInertia_key (N := N) l P σ i (fun x => by
      have h₁ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
        (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩ x
      simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁
      have h2 := hi (Ideal.Quotient.mk P x)
      rwa [h₁, Int.card_ideal_quot] at h2)
    exact ⟨i, by simpa using this.symm⟩
  · rw [cycInertia_card_map, Ideal.card_stabilizer_eq (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, (cycInertia_ef (N := N) l).2, decompUnits,
      cycInertia_card_comap, Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective,
      Units.coeHom_apply, ZMod.coe_unitOfCoprime]

private theorem cycInertia_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
    (x : K) : φ (σ x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change φ (σ _) = starRingEnd ℂ (φ _)
    have h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1 :=
      (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)
    rw [← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact DFunLike.congr_fun key x

theorem card_fieldChars (E : IntermediateField ℚ K) :
    Nat.card (fieldChars N E) = Module.finrank ℚ E ∧
      (IsTotallyReal E ↔ ∀ ψ ∈ fieldChars N E, ψ.Even) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  have hmem : ∀ ψ, ψ ∈ fieldChars N E ↔
      ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
    intro ψ
    rw [fieldChars, mem_annihilator_iff]
    constructor
    · intro h σ hσ
      exact h _ ⟨σ, hσ, rfl⟩
    · rintro h _ ⟨σ, hσ, rfl⟩
      exact h σ hσ
  have heq : fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
    ext ψ
    rw [hmem, mem_intermediateFieldEquivSubgroupChar_iff]
  refine ⟨by rw [heq, card_intermediateFieldEquivSubgroupChar], ?_⟩
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  have heq2 : fieldChars N E = (subgroupGalEquivSubgroupChar N K ℂ E.fixingSubgroup).ofDual := by
    ext ψ
    rw [hmem, mem_subgroupGalEquivSubgroupChar_iff]
  clear hmem heq
  generalize fieldChars N E = X at heq2 ⊢
  have h1 : σ ∈ E.fixingSubgroup ↔ ∀ ψ ∈ X, ψ.Even := by
    have := mem_subgroupGalEquivSubgroupChar_symm_iff N K ℂ σ X
    rw [hσ] at this
    conv_lhs at this => rw [heq2, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]
    simpa [DirichletCharacter.Even] using this
  rw [← h1, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    apply φ.injective
    rw [cycInertia_conj σ hσ]
    have := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))
    rw [ComplexEmbedding.isReal_iff] at this
    exact RingHom.congr_fun this ⟨x, hx⟩
  · intro h
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← ComplexEmbedding.lift_algebraMap_apply K w.embedding,
      ← cycInertia_conj σ hσ]
    congr 1
    exact h x x.2

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.RootNorm
section
namespace KStar.Ram

open NumberField

private theorem rootNorm_powerBasis {F : Type*} [Field F] [Algebra ℚ F] (pb : PowerBasis ℚ F) :
    Algebra.norm ℚ (1 - pb.gen) = (minpoly ℚ pb.gen).eval 1 := by
  classical
  rw [← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one, map_one]

private theorem rootNorm_field {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ k : ℕ, Module.finrank ℚ K = (minpoly ℚ x).natDegree * k ∧
      Algebra.norm ℚ (1 - x) = ((minpoly ℚ x).eval 1) ^ k := by
  have hx : IsIntegral ℚ x := .of_finite ℚ x
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩
  · rw [← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]
  · have h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K
        (1 - IntermediateField.AdjoinSimple.gen ℚ x) := by
      simp
    have h2 := rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h2
    rw [h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]
    exact congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2

theorem padicValNat_absNorm_one_sub {K : Type*} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime]
    {m : ℕ} (hm : 2 ≤ m) {η : 𝓞 K} (hη : IsPrimitiveRoot η m) :
    (padicValNat l (Ideal.absNorm (Ideal.span {1 - η})) : ℚ) =
      Module.finrank ℚ K * rootWeight l m := by
  haveI : NeZero m := ⟨by omega⟩
  have hηK : IsPrimitiveRoot (η : K) m :=
    hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨k, hk, hnorm⟩ := rootNorm_field (η : K)
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic] at hk
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)] at hnorm
  have hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ) := by
    rw [← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast,
      Int.cast_one]
  have hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]
    push_cast
    rfl
  have hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) =
      m.totient * rootWeight l m := by
    by_cases hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)
    · obtain ⟨p, j, hp, rfl⟩ := hpp
      haveI := Fact.mk hp
      rw [Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]
      have hne : p ^ (j + 1) ≠ 1 := fun h => by rw [h] at hm; norm_num at hm
      by_cases hpl : p = l
      · subst hpl
        rw [Nat.padicValNat_def, Nat.Prime.multiplicity_self, rootWeight,
          if_pos ⟨hne, j + 1, rfl⟩]
        have ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne'
        rw [Nat.cast_one, mul_one_div, div_self ht]
      · rw [Nat.padicValNat_def, multiplicity_primes (Ne.symm hpl), rootWeight, if_neg]
        · simp
        · rintro ⟨-, s, hs⟩
          apply hpl
          rcases s with _ | s
          · rw [pow_zero] at hs
            exact absurd hs hne
          · have hd : p ∣ l ^ (s + 1) := by
              rw [← hs]
              exact dvd_pow_self p (Nat.succ_ne_zero j)
            exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)
    · have h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1 := by
        apply Polynomial.eval_one_cyclotomic_not_prime_pow
        intro p hp j hj
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · exact hpp ⟨p, j, hp, hj.symm⟩
      rw [h1, rootWeight, if_neg]
      · simp [_root_.Nat.padicValNat_def (n := 1)]
      · rintro ⟨-, s, hs⟩
        rcases s with _ | s
        · rw [pow_zero] at hs
          omega
        · exact hpp ⟨l, s, Fact.out, hs⟩
  rw [Nat.padicValNat_def] at hv
  rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, Nat.padicValNat_def,
    Nat.multiplicity_pow, hk, Nat.cast_mul, Nat.cast_mul, hv]
  ring

end KStar.Ram
end

