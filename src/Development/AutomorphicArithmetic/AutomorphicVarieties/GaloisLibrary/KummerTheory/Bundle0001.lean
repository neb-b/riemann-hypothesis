module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0007
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem index_range_eq_card_ker {T : Type*} [CommGroup T] [Finite T] (f : T →* T) :
    f.range.index = Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_mul_index f.ker
  have hk : f.ker.index = Nat.card f.range := by
    show Nat.card (T ⧸ f.ker) = _
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hk] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range * f.range.index = Nat.card f.range * Nat.card f.ker := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

private theorem mem_unit_of_pow_mem {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {p : ℕ}
    (hp : p ≠ 0) {b : Kˣ} (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have h := hb v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h
  simpa [hp] using h

private theorem powK_subgroupOf {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ}
    (hp : p ≠ 0) : (powK (K := K) p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext x
  rw [Subgroup.mem_subgroupOf, powK.eq_1, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [powMonoidHom_apply] at hb
    have hbS : b ∈ S.unit K := mem_unit_of_pow_mem hp (by rw [hb]; exact x.2)
    refine ⟨⟨b, hbS⟩, ?_⟩
    apply Subtype.ext
    simpa using hb
  · rintro ⟨c, hc⟩
    refine ⟨c.1, ?_⟩
    rw [← hc]
    simp

private theorem card_ker_eq {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom n : CommGroup.torsion (S.unit K) →* CommGroup.torsion (S.unit K)).ker =
      Nat.card (rootsOfUnity n K) := by
  have hfin : ∀ ζ : rootsOfUnity n K, IsOfFinOrder (ζ : Kˣ) := fun ζ =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, (mem_rootsOfUnity _ _).mp ζ.2⟩
  have hS : ∀ ζ : rootsOfUnity n K, (ζ : Kˣ) ∈ S.unit K := fun ζ v _ =>
    GroundTheory.Global.SUnit.valuation_eq_one_of_isOfFinOrder (hfin ζ) v
  refine Nat.card_congr
    { toFun := fun t => ⟨t.1.1.1, (mem_rootsOfUnity _ _).mpr (by
        have h := congrArg (fun y : CommGroup.torsion (S.unit K) => ((y : S.unit K) : Kˣ))
          (MonoidHom.mem_ker.mp t.2)
        simpa using h)⟩
      invFun := fun ζ => ⟨⟨⟨ζ.1, hS ζ⟩, (CommGroup.mem_torsion _).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)⟩)⟩,
        MonoidHom.mem_ker.mpr (Subtype.ext (Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem UpperTheory.V.Kum.cardSUnit :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n], S.Finite → Nat.card (S.unit K ⧸ (powK (K := K) n).subgroupOf (S.unit K)) = n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 + Nat.card S) * Nat.card (rootsOfUnity n K) := by
  intro K _ _ S n _ hS
  haveI : Finite S := hS
  rw [← Subgroup.index_eq_card, powK_subgroupOf S (NeZero.ne n),
    GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), GroundTheory.Global.SUnit.finrank_quotient_torsion,
    index_range_eq_card_ker, card_ker_eq, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem clMapBasic_mem {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K')
    (I : Ideal (𝓞 K)) (y : 𝓞 K') :
    y ∈ I.map (RingOfIntegers.mapRingEquiv τ) ↔ ∃ x ∈ I, RingOfIntegers.mapRingEquiv τ x = y :=
  Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective

private theorem clMapBasic_lemma {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) :
    clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = Ideal.map _ (Ideal.map _ _)
  ext y
  rw [clMapBasic_mem, clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, (clMapBasic_mem τ _ _).mpr ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (clMapBasic_mem τ _ _).mp hz
    exact ⟨x, hx, rfl⟩
private theorem clMap_refl_apply {K : Type} [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = _
  ext y
  rw [clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem UpperTheory.V.Kum.clMapBasic :
    ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K''),
    (∀ c, clMap (RingEquiv.refl K) c = c) ∧ (∀ c, clMap (τ.trans τ') c = clMap τ' (clMap τ c)) ∧ Function.Bijective (clMap τ) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K')), (∀ x, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ w.asIdeal) → clMap τ (primeCl v) = primeCl w := by
  intro K K' K'' _ _ _ _ _ _ τ τ'
  refine ⟨clMap_refl_apply, clMapBasic_lemma τ τ', ?_, ?_⟩
  · have hl : ∀ c, clMap τ.symm (clMap τ c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.self_trans_symm, clMap_refl_apply]
    have hr : ∀ c, clMap τ (clMap τ.symm c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.symm_trans_self, clMap_refl_apply]
    exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
  · intro v w hvw
    unfold primeCl
    rw [class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map _ _ = _
    ext y
    rw [clMapBasic_mem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hvw x).mp hx
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv τ).symm y, ?_, ?_⟩
      · rw [hvw, RingEquiv.apply_symm_apply]
        exact hy
      · exact RingEquiv.apply_symm_apply _ y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mk_eq_finprod (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1 := by
  let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
      fun v hv h => hv (by simp only [h, zpow_zero])
  have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
    apply Units.ext
    rw [← Units.coeHom_apply, map_finprod _ hfin]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
  conv_lhs => rw [← hI]
  rw [map_finprod _ hfin]
  exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl

private theorem count_eq_ordv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a := by
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
    simpa using nonZeroDivisors.coe_ne_zero _
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
  simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
  ring

theorem UpperTheory.V.Kum.clProd :
    ∀ (K : Type) [Field K] [NumberField K], (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ), FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a) ∧ (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) ∧ ∀ a : Kˣ, radCl 1 a = 1 := by
  intro K _ _
  refine ⟨mk_eq_finprod K, count_eq_ordv K, fun a => ?_, fun a => ?_⟩
  · simp only [← count_eq_ordv]
    exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · have h := mk_eq_finprod K (toPrincipalIdeal (𝓞 K) K a)
    rw [coe_toPrincipalIdeal] at h
    simp only [count_eq_ordv] at h
    simp only [radCl, Nat.cast_one, Int.ediv_one]
    rw [← h, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).2 ⟨_, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClSubUniv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.clSubUniv :
    ∀ (K : Type) [Field K] [NumberField K], clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  intro K _ _
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd hI (zero_notMem_nonZeroDivisors)
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      have : (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 := Subtype.ext Ideal.one_eq_top.symm
      rw [this, map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp0 : p ≠ 0 := hp.ne_zero
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp0
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ ?_ (ih ha')
      have hpr : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hp0⟩
      have hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩ := rfl
      rw [← hv]
      exact Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective x
  exact key I hI
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.cobOfGen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (γ : Γ),
    Continuous χ → ContAction ρ → (∀ g, χ g = 1 → ∀ m, ρ g m = m) → (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) → (Function.Surjective fun m => ρ γ m - m) →
    ∀ z ∈ Z1 ρ, (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ram_one {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  have : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl
  have : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  have := v.isMaximal
  have : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ) (hb : b ^ n = algebraMap K L a) :
    (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [h, pow_one, ← hb, map_pow,
    ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1
      exact WithZero.coe_ne_zero h1
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

private theorem dvd_fin {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal] (n : ℕ) (b : E) (a : Kˣ)
    (hb : b ^ n = algebraMap K E a) (h : ∀ τ ∈ P.inertia (E ≃ₐ[K] E), τ b = b) : (n : ℤ) ∣ ordv v a := by
  let L : IntermediateField K E := IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))
  have hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL : b ∈ L := (IntermediateField.mem_fixedField_iff _ _).2 h
  have : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)

theorem UpperTheory.V.Kum.dvdOfIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ), IsPlaceOver A v → β ^ n = algebraMap K Ω a → (∀ g ∈ Ine (F := K) A, g β = β) → (n : ℤ) ∣ ordv v a := by
  intro K Ω _ _ _ _ _ n A v β a hA hβ hI
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  have : NumberField L := NumberField.of_module_finite K _
  have hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  have : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have hm : (CompanionTheory.PlaceDict.cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap (𝓞 K) (𝓞 Ω))
      (algebraMap_isIntegral_iff.mpr this) _ (by
      have := v.isMaximal
      rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (CompanionTheory.PlaceDict.cen A).under (𝓞 L)
  have : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  refine dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_
  obtain ⟨φ, h1, h2⟩ := CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact hτ x
  obtain ⟨h3, h4⟩ := CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
  rw [← h1]
  exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.X ^ k - 1 : Polynomial F).rootSet Ω = {b : Ω | ∃ m ∈ ({k} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
  have hp : (Polynomial.X ^ k - 1 : Polynomial F) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : F)
  ext b
  rw [Polynomial.mem_rootSet_of_ne hp]
  simp [sub_eq_zero, hk]

private theorem apply_mem_fn_of_isLift (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l n : ℕ) (τ : F ≃+* F)
    (σ : Ω ≃+* Ω) (h : IsLift τ σ) (x : Ω) (hx : x ∈ Fn F Ω l n) : σ x ∈ Fn F Ω l n := by
  have hx' : x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω) := hx
  show σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)
  refine IntermediateField.adjoin_induction F
    (motive := fun x _ => σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω))
    ?_ ?_ ?_ ?_ ?_ hx'
  · intro y hy
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet] at hy ⊢
    obtain ⟨hp, hy⟩ := hy
    refine ⟨hp, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at hy ⊢
    rw [← map_pow, ← map_one σ, ← map_sub, hy, map_zero]
  · intro c
    rw [h c]
    exact IntermediateField.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact add_mem hy hz
  · intro y _ hy
    rw [map_inv₀]
    exact inv_mem hy
  · intro y z _ _ hy hz
    rw [map_mul]
    exact mul_mem hy hz

theorem UpperTheory.V.Kum.fnCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) ∧ (∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∃ τ' : Fn F Ω l n ≃+* Fn F Ω l n, IsLift τ' σ) ∧ (2 ≤ n → IsTotallyComplex (Fn F Ω l n)) := by
  intro F Ω _ _ _ _ _ l _ n
  have hl : l.Prime := Fact.out
  have hk : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hk⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hFn : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ m ∈ ({l ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    show IntermediateField.adjoin F _ = _
    rw [rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton F Ω _ hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (S := {l ^ n}) (K := F) (L := Ω) ?_
    intro m hm _
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  · intro τ σ h
    have hs : IsLift τ.symm σ.symm := by
      intro x
      apply σ.injective
      rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
    refine ⟨{ toFun := fun x => ⟨σ x, apply_mem_fn_of_isLift F Ω l n τ σ h x.1 x.2⟩,
              invFun := fun x => ⟨σ.symm x, apply_mem_fn_of_isLift F Ω l n τ.symm σ.symm hs x.1 x.2⟩,
              left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1),
              right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1),
              map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1),
              map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }, ?_⟩
    intro x
    rfl
  · intro hn2
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hzmem : z ∈ Fn F Ω l n := by
      rw [hFn]
      exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, rfl, hk, hz.pow_eq_one⟩
    have hζ : IsPrimitiveRoot (⟨z, hzmem⟩ : Fn F Ω l n) (l ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Fn F Ω l n).val) hz Subtype.val_injective
    have hcyc := IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) hζ
    have h2 : 2 < l ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hl.pos hn2
    have htc := @IsCyclotomicExtension.Rat.isTotallyComplex (l ^ n) _
      (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) _ _ hcyc h2
    exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) (Fn F Ω l n)
end

