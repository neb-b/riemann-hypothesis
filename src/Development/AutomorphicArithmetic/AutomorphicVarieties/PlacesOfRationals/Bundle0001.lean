module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Minkowski
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

open CompanionTheory.PlaceDict in
private theorem exists_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [Algebra.IsAlgebraic E Ω] (L : IntermediateField E Ω) [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ A : ValuationSubring Ω, (cen A).IsMaximal ∧ (cen A).under (𝓞 L) = w.asIdeal := by
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  exact ⟨A, hQ, hw⟩

open CompanionTheory.PlaceDict in
private theorem lift_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  obtain ⟨A, hm, hw⟩ := exists_over L w
  obtain ⟨φ, h1, h2⟩ := lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact (hw.ge (hτ x) :)
  obtain ⟨h3, h4⟩ := of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

open scoped nonZeroDivisors Pointwise in
private theorem finite_case (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    (S : Subgroup (M ≃ₐ[ℚ] M))
    (h : ∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[ℚ] M) ≤ S) : S = ⊤ := by
  set F : IntermediateField ℚ M := IntermediateField.fixedField S with hF
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra hne
    obtain ⟨Q, hQ, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne
    apply hram
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 M)))
    have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P Q
    have hG : IsGaloisGroup S F M := IsGaloisGroup.subgroup (M ≃ₐ[ℚ] M) ℚ M S
    have hG' : IsGaloisGroup S (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing S _ _ F M
    have hG0 : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
    have e1 := Ideal.card_inertia_eq_ramificationIdxIn (G := S) Q P
    have e2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (P.under ℤ) P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P S] at e1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[ℚ] M)] at e2
    have e3 : Nat.card (P.inertia S) = Nat.card (P.inertia (M ≃ₐ[ℚ] M)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h P hPmax)).toEquiv]
      rfl
    have e4 : P.ramificationIdx ℤ = Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
      Ideal.ramificationIdx_tower Q P
    have e5 : 0 < P.ramificationIdx (𝓞 F) := P.ramificationIdx_pos _
    rw [← Ideal.ramificationIdx_eq_one_iff]
    have e6 : Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) = 1 * P.ramificationIdx (𝓞 F) := by
      rw [← e4, ← e2, ← e3, e1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right e5 e6
  have h2 : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField S, ← hF, h2, IntermediateField.fixingSubgroup_bot]

open IntermediateField in
private theorem general {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ (M : Type) [Field M] [NumberField M] [Algebra E M] [IsGalois E M] (S : Subgroup (M ≃ₐ[E] M)),
      (∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[E] M) ≤ S) → S = ⊤)
    (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal) (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ A : ValuationSubring Ω, Ine (F := E) A ≤ H) : H = ⊤ := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hfix : (fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  generalize fixedField H = L at hfix
  subst hfix
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite _).1 ho
  have : IsGalois E L := (InfiniteGalois.normal_iff_isGalois _).1 hn
  have : NumberField L := NumberField.of_module_finite E _
  have hb : (⊥ : Subgroup (L ≃ₐ[E] L)) = ⊤ := hE L ⊥ fun P hP τ hτ => by
    let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField L)⟩
    obtain ⟨A, φ, h1, h2⟩ := lift_ine L w τ hτ
    rw [Subgroup.mem_bot, ← h1, ← MonoidHom.mem_ker, restrictNormalHom_ker]
    exact hI A h2
  rw [eq_top_iff, ← restrictNormalHom_ker]
  intro g _
  rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, hb]
  trivial

theorem UpperTheory.V.B3.minkowski :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)), N.Normal → IsOpen (N : Set (G ℚ Ω)) →
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ N) → N = ⊤ := by
  intro Ω _ _ _ N hn ho hI
  refine general (fun M _ _ inst hG S hS => ?_) N hn ho hI
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact finite_case M S hS
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)]
  simpa using h

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

private theorem eq_vQ {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v = vQ hl := by
  apply HeightOneSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le (vQ hl).isMaximal v.isPrime.ne_top
  show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact h

private theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  set J : Ideal ℤ := v.asIdeal.comap (Int.castRingHom (𝓞 ℚ)) with hJ
  have hJp : J.IsPrime := Ideal.IsPrime.comap _
  have hJb : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hxe : ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) = x := by
      conv_rhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
      exact (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
    have hmem : Rat.ringOfIntegersEquiv x ∈ J := by
      rw [hJ, Ideal.mem_comap]
      simpa [hxe] using hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    rw [← hxe, hmem]
    simp
  obtain ⟨z, hzJ, hz⟩ := hJp.exists_mem_prime_of_ne_bot hJb
  refine ⟨z.natAbs, Int.prime_iff_natAbs_prime.mp hz, ?_⟩
  have hz' : ((z.natAbs : ℤ)) ∈ J := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]; exact hzJ
    · have : ((z.natAbs : ℤ)) = -z := by omega
      rw [this]; exact J.neg_mem hzJ
  rw [hJ, Ideal.mem_comap] at hz'
  simpa using hz'

theorem UpperTheory.V.B3.placesQ :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ B.valuation (p : Ω) < 1) ∧
    ∀ (p : ℕ) (A B : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → B.valuation (p : Ω) < 1 →
      ∃ g : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) B, g⁻¹ * x * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have val_top {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2
  have int_le (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2
  have hTop : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hOver (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
      ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v := by
    have hm : ∀ x : 𝓞 ℚ, algebraMap ℚ Ω (x : ℚ) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap ℚ Ω).toIntAlgHom))
    let f : 𝓞 ℚ →+* A := ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)).codRestrict A hm
    let P : Ideal (𝓞 ℚ) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 ℚ, A.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ ℚ := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℚ)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5
  have hNe (A : ValuationSubring Ω) (N : ℕ) (hN : N ≠ 0)
      (h : A.valuation (N : Ω) < 1) : A ≠ ⊤ := by
    intro he
    subst A
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  have hIff (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ)
      (hv : IsPlaceOver A v) : A.valuation (N : Ω) < 1 ↔ ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have h := hv (N : 𝓞 ℚ)
    have e : algebraMap ℚ Ω ((N : 𝓞 ℚ) : ℚ) = (N : Ω) := by simp
    rw [← e]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := ℚ) Ω (vQ hp)
    refine ⟨A, (hIff A (vQ hp) p hA).mpr ?_⟩
    show ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.span {((p : ℕ) : 𝓞 ℚ)}
    exact Ideal.subset_span rfl
  · intro B
    by_cases hB : B = ⊤
    · left
      rw [hB]
      exact hTop
    · right
      obtain ⟨v, hv⟩ := hOver B hB
      obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
      exact ⟨p, hp, (hIff B v p hv).mpr hpv⟩
  · intro p A B hp hA hB
    obtain ⟨vA, hvA⟩ := hOver A (hNe A p hp.ne_zero hA)
    obtain ⟨vB, hvB⟩ := hOver B (hNe B p hp.ne_zero hB)
    have eA := eq_vQ hp vA ((hIff A vA p hvA).mp hA)
    have eB := eq_vQ hp vB ((hIff B vB p hvB).mp hB)
    subst eA
    rw [eB] at hvB
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hvA hvB
    refine ⟨σ, fun x hx => ?_⟩
    rw [← hσ] at hx
    exact GlobalTheory.Cut.ShaBound.conj_mem_Ine' hx
end

