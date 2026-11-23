module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGaloisOfIsRayFieldTop
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.RayTopGalois

theorem count_comap {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

section Transport

variable {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N] [NumberField N]
  [Algebra K N] [Algebra K' N] (s : K ≃+* K') (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x)

def autEquiv : (N ≃ₐ[K] N) ≃* (N ≃ₐ[K'] N) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := s.surjective x
    rw [hs]; exact σ.commutes y
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    rw [← hs]; exact σ.commutes _
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s)

include hs in
omit [NumberField K] [NumberField K'] [NumberField N] in
theorem liesOver_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 N)) :
    P.LiesOver (primeEquiv s 𝔭).asIdeal ↔ P.LiesOver 𝔭.asIdeal := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K') (𝓞 N) (RingOfIntegers.mapRingEquiv s x) = algebraMap (𝓞 K) (𝓞 N) x :=
    fun x => RingOfIntegers.ext (hs x)
  have h2 : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv s x ∈ (primeEquiv s 𝔭).asIdeal ↔ x ∈ 𝔭.asIdeal := fun x => by
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s x) ∈ 𝔭.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩, fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩⟩
  · rw [← h2, H, Ideal.mem_under, Ideal.mem_under, h]
  · obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    rw [h2, H, Ideal.mem_under, Ideal.mem_under, h]

theorem absNorm_primeEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (primeEquiv s 𝔭).asIdeal = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s) ?_).toEquiv).symm
  exact (Ideal.map_comap_of_equiv _).symm

omit [NumberField N] in
theorem isFrob_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    IsFrob N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ IsFrob N 𝔭 σ := by
  unfold IsFrob
  rw [absNorm_primeEquiv]
  exact exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

omit [NumberField K] [NumberField K'] [NumberField N] in
theorem inInertia_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    InInertia N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ InInertia N 𝔭 σ :=
  exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

theorem heckeVal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal N χ (primeEquiv s 𝔭) = heckeVal N (χ.comp (autEquiv s hs).toMonoidHom) 𝔭 := by
  by_cases h : ∀ τ, InInertia N (primeEquiv s 𝔭) τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob N 𝔭
    rw [heckeVal_eq N _ 𝔭 (fun τ hτ => h _ ((inInertia_iff' s hs 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq N χ _ h ((isFrob_iff' s hs 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero N χ _ h, heckeVal_eq_zero N _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := (autEquiv s hs).surjective τ
    exact h' σ ((inInertia_iff' s hs 𝔭 σ).1 hτ)

theorem heckeIdeal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) {a : 𝓞 K} (ha : a ≠ 0) :
    heckeIdeal N χ (Ideal.span {RingOfIntegers.mapRingEquiv s a}) =
      heckeIdeal N (χ.comp (autEquiv s hs).toMonoidHom) (Ideal.span {a}) := by
  have e : Ideal.span {RingOfIntegers.mapRingEquiv s a} =
      (Ideal.span {a}).comap (RingOfIntegers.mapRingEquiv s).symm := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    rfl
  unfold heckeIdeal
  rw [← finprod_comp_equiv (primeEquiv s)]
  refine finprod_congr fun 𝔭 => ?_
  rw [heckeVal_transport s hs, e, count_comap _ _ (by simpa using ha)]


include hs in
theorem isModulus_top_transport [IsGalois K N] [IsGalois K' N] (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ ⊤)
    (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ ⊤ := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    exact (h _).2.1 𝔮 fun h => 𝔮.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _, hc _, trivial, fun φ => ?_⟩
    have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
    change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
    rwa [s.symm_apply_apply, s.symm_apply_apply] at this

include hs in
omit [NumberField K] [NumberField K'] in
theorem isAbelianGalois_transport [CharZero K] [IsAbelianGalois K N] : IsAbelianGalois K' N := by
  have : IsGalois K' N := IsGalois.of_equiv_equiv (f := s) (g := RingEquiv.refl N) (RingHom.ext hs)
  have : IsMulCommutative (N ≃ₐ[K'] N) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (autEquiv s hs).surjective a
    obtain ⟨b, rfl⟩ := (autEquiv s hs).surjective b
    rw [← map_mul, ← map_mul, mul_comm' a b]⟩⟩
  exact {}

end Transport

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    (h : IsRayField L N ⊤) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hab := h.1
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab ⊤ ⊤ h.2 dvd_rfl top_ne_bot
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' ⊤ top_ne_bot h.2
    (@isModulus_top_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRayField_top : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L],
    GlobalTheory.Mem.Fld.IsRayField L N ⊤ → IsGalois K N := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ h
  have hab := h.1
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GlobalTheory.RayTopGalois

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsModulusTopOfIsTotallyComplex
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.Chr GlobalTheory.Mem.LocTriv GlobalTheory.RayFromArtin
open scoped nonZeroDivisors

namespace GlobalTheory.UnramModulus

theorem inInertia_restrict {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : Type) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G K Ω}
    (hσ : σ ∈ Ine (F := K) A) : GlobalTheory.NT.InInertia L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_sub] at this
    exact this

theorem rayIdl_le {K : Type} [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) {U : Subgroup (Neutral.B1.Ideles K)}
    (ho : IsOpen (U : Set (Neutral.B1.Ideles K))) (hi : infConn K ≤ U)
    (hu : ∀ v x, Formalism.L2.Host.IsUnitAt v x → Neutral.B1.localIdele K v x ∈ U) : rayIdl 𝔪 ≤ U := by
  rintro b ⟨hb, -, hb'⟩
  let c : Neutral.B1.Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)
  have e : b = c * finPartI K b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [e]
  refine mul_mem (hi ⟨_, hb', rfl⟩) ?_
  refine (U.isClosed_of_isOpen ho).mem_of_tendsto
    (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)
  exact Subgroup.prod_mem _ fun v _ => hu v _ (hb v)

theorem isModulus_top (H : GlobalTheory.Published.GlobalArtinReciprocity) (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭)
    (χ : (M ≃ₐ[K] M) →* ℂˣ) : GlobalTheory.NT.IsModulus M χ ⊤ := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := H K Ω
  let j : M →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra M Ω := j.toRingHom.toAlgebra
  have : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : CommGroup (M ≃ₐ[K] M) := { (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }
  let φ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hφ : Continuous φ := by
    refine continuous_of_isOpen_ker' φ ?_
    have : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen
    ext x
    apply (algebraMap M Ω).injective
    exact (σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)
  let θ : Neutral.B1.Ideles K →* (M ≃ₐ[K] M) := (liftAb φ hφ).comp art
  have hθ : Continuous θ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (θ.ker : Set (Neutral.B1.Ideles K)) := (isOpen_discrete {1}).preimage hθ
  have hk : (Neutral.B1.diagUnits K).range ⊔ infConn K ≤ θ.ker := fun x hx => by
    have hk : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have hr : rayGrp ⊤ ≤ θ.ker := by
    refine sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]
    exact hM v _ (inInertia_restrict M hA hτ)
  let ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M) := (θ.comp (unifIdl ⊤))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h)) := fun v hv => by
    refine ⟨hM v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
    have : ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ := by
      rw [MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply,
        ← e', liftAb_toAb, map_inv, inv_inv]
    rw [this]
    exact isFrob_restrict M hA hσ
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩
  · obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob M 𝔭
    rw [GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]
    exact Units.ne_zero _
  · have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr'.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr'.2.1
    obtain ⟨A, hA'⟩ := exists_integral ⊤ _ ha0 hr'.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral ⊤ _ hb0 hr'.2.2.2.1
    rw [heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']
    have h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K))) := by
      rw [Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast hr'.1
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hr'.2.1
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    have h2 : ψ (B⁻¹ * A) = 1 := by
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]

theorem isModulus_top_of_isTotallyComplex : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (K M : Type) [Field K]
    [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M],
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭) → ∀ χ : (M ≃ₐ[K] M) →* ℂˣ, GlobalTheory.NT.IsModulus M χ ⊤ :=
  fun H K M _ _ _ _ _ _ _ hM χ => isModulus_top H K M hM χ

end GlobalTheory.UnramModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def IsNeg (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Prop := (-(Yᴴ * Jm P Q * Y)).PosDef

def matA (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ := Y.toRows₁ * (Y.toRows₂)⁻¹

def linX (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim (v ∘ Sum.inl - matA Y *ᵥ (v ∘ Sum.inr)) ((φ ∘ Sum.inl) ᵥ* matA Y + φ ∘ Sum.inr)

def scal (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : ℂ :=
  (Y.toRows₂.det)⁻¹ * Complex.exp (-((linX Y v φ ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)))

def ker (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ)
    (v' φ' : Ix P Q → ℂ) : ℂ :=
  ((-(Yᴴ * Jm P Q * Y')).det)⁻¹ * Complex.exp ((star v ᵥ* Jm P Q) ⬝ᵥ v' -
    (star v ᵥ* Jm P Q + φ') ⬝ᵥ (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) *ᵥ (Jm P Q *ᵥ star φ + v'))

def baseY (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Ix P Q) (Fin Q) ℂ := Matrix.fromRows A 1

def baseV (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim (x ∘ Sum.inl) 0

def baseF (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim 0 (x ∘ Sum.inr)

def dA (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ :=
  Z.toBlocks₁₁ * A + Z.toBlocks₁₂ - A * (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)

def dX (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim ((Z.toBlocks₁₁ - A * Z.toBlocks₂₁) *ᵥ (x ∘ Sum.inl))
    (-((x ∘ Sum.inr) ᵥ* (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)))

def dS (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : ℂ :=
  -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂).trace - (x ∘ Sum.inr) ⬝ᵥ Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)

theorem toRows₂_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : (baseY A).toRows₂ = 1 := rfl

theorem matA_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : matA (baseY A) = A := by
  simp [matA, baseY]

theorem linX_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : linX (baseY A) (baseV x) (baseF x) = x := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  have h2 : baseF x ∘ Sum.inl = 0 := rfl
  rw [linX, h1, h2]
  ext (i | j) <;> simp [baseV, baseF]

theorem scal_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : scal (baseY A) (baseV x) (baseF x) = 1 := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  simp [scal, h1, toRows₂_baseY]

theorem form_blocks (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * Y'.toRows₂ - Y.toRows₁ᴴ * Y'.toRows₁ := by
  conv_lhs => rw [← Matrix.fromRows_toRows Y, ← Matrix.fromRows_toRows Y']
  rw [Jm, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem frame_eq (Y : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) :
    Y = baseY (matA Y) * Y.toRows₂ := by
  rw [baseY, Matrix.fromRows_mul, matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one,
    Matrix.one_mul, Matrix.fromRows_toRows]

theorem form_factor (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) (h' : IsUnit Y'.toRows₂.det) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
  have e : ∀ Y : Matrix (Ix P Q) (Fin Q) ℂ, IsUnit Y.toRows₂.det → matA Y * Y.toRows₂ = Y.toRows₁ := fun Y h => by
    rw [matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  rw [form_blocks, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    e Y h, Matrix.mul_assoc, e Y' h']

theorem isNeg_baseY {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) : IsNeg (baseY A) := by
  rw [IsNeg, form_blocks]
  simpa [baseY] using h

theorem IsNeg.isUnit {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : IsUnit Y.toRows₂.det := by
  rw [IsNeg, form_blocks] at h
  have h2 := h.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y.toRows₁)
  rw [sub_add_cancel] at h2
  have h3 := h2.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

theorem IsNeg.posDef {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : (1 - (matA Y)ᴴ * matA Y).PosDef := by
  have hu := h.isUnit
  rw [IsNeg, form_factor Y Y hu hu] at h
  have hu' : IsUnit Y.toRows₂ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact (hu'.posDef_star_left_conjugate_iff).1 h

theorem form_mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    (g * Y)ᴴ * Jm P Q * (g * Y') = Yᴴ * Jm P Q * Y' := by
  rw [Matrix.conjTranspose_mul]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

theorem IsNeg.mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) :
    IsNeg (g * Y) := by
  rwa [IsNeg, form_mul hg]

theorem Jm_mul_Jm : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem ker_mul {g g' : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (hg' : g' * g = 1)
    (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : Ix P Q → ℂ) :
    ker (g * Y) (g *ᵥ v) (φ ᵥ* g') (g * Y') (g *ᵥ v') (φ' ᵥ* g') = ker Y v φ Y' v' φ' := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg'
  have h1 : gᴴ * Jm P Q = Jm P Q * g' := by
    conv_rhs => rw [← hg, Matrix.mul_assoc, hg2, Matrix.mul_one]
  have h0 : g' = Jm P Q * gᴴ * Jm P Q := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have hJ : (Jm P Q)ᴴ = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h2 : Jm P Q * g'ᴴ = g * Jm P Q := by
    rw [h0, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have e1 : star (g *ᵥ v) ᵥ* Jm P Q = (star v ᵥ* Jm P Q) ᵥ* g' := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1]
  have e2 : Jm P Q *ᵥ star (φ ᵥ* g') = g *ᵥ (Jm P Q *ᵥ star φ) := by
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
  have e3 : g * Y' * (Yᴴ * Jm P Q * Y')⁻¹ * (g * Y)ᴴ * Jm P Q =
      g * (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) * g' := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h1]
  have e4 : ∀ (u w : Ix P Q → ℂ) (M : Mat P Q), (u ᵥ* g') ⬝ᵥ (g * M * g') *ᵥ (g *ᵥ w) = u ⬝ᵥ M *ᵥ w := by
    intro u w M
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg', Matrix.mul_one]
  rw [ker, ker, form_mul hg, e1, e2, e3, ← Matrix.add_vecMul, ← Matrix.mulVec_add, e4, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem isSchemeTheoreticallyDominant_compl_of_effCartier :
    ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I →
      IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  intro W I hI
  choose U f hxU hf hIU using hI
  refine ⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · have h0 := Scheme.Hom.ideal_ker_le _ (U x) hs
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at h0
    have hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X := W) I.support.compl) ''ᵁ
        ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by
      intro y hy
      have hyU : y ∈ (U x).1 := W.basicOpen_le (f x) hy
      have hyc : y ∈ I.support.compl := by
        intro hy'
        have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
        rw [Scheme.mem_zeroLocus_iff] at this
        exact this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy
      exact ⟨⟨y, hyc⟩, hyU, rfl⟩
    have := (U x).2.isLocalization_basicOpen (f x)
    have hinj := IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x))
      ((Submonoid.powers_le).2 (hf x))
    have h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0 := by
      have h2 := congrArg (W.presheaf.map (homOfLE hle).op).hom h0
      have h3 := h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)
      refine Eq.trans ?_ h3
      erw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have : s = 0 := hinj (by rw [h1, map_zero])
    simp [this]

end GlobalTheory.ProjBlowup
end

