module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

section Alg

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

private theorem algebraMap_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hne
  have hbot : (⊥ : Ideal O).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l])
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]
    exact hmax
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

private theorem length_quot [Module.Free ℤ_[l] O] : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, ← IsLocalRing.finrank_quotient_map (R := ℤ_[l]) (S := O)]
  letI : Field (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l])
      (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

end Alg

theorem UpperTheory.V.Base.dvrFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧
      eO l O = Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) ∧ eO l O ≠ 0 ∧
      eO l O ≤ (Module.finrank ℤ_[l] O : ℕ∞) ∧ eO l O = IsDiscreteValuationRing.addVal O (l : O) ∧
      ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : O) := by
  intro l _ O _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := algebraMap_inj O
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  obtain ⟨hcomp, -, hlm, -, hfree, hloc⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfree
  haveI := hloc
  have hspan : Ideal.span {(l : O)} =
      (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by
      rw [map_natCast, h, map_zero]
    have h'' : ((l : ℕ) : ℤ_[l]) = 0 := hinj h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h'')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hval : IsDiscreteValuationRing.addVal O (l : O) = n :=
    IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  have he : eO l O = n := by
    show Module.length O (O ⧸ Ideal.span {(l : O)}) = n
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hlm (hu ▸ u.isUnit)
  refine ⟨hinj, hfree, hloc, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · show Module.length O (O ⧸ Ideal.span {(l : O)}) = _
    rw [hspan]
  · rw [he]
    exact_mod_cast hn0
  · rw [← length_quot (l := l) O]
    show Module.length O (O ⧸ Ideal.span {(l : O)}) ≤ _
    rw [IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)})]
    exact le_mul_of_one_le_right' (Order.one_le_iff_pos.2 Module.length_pos)
  · rw [he, hval]
  · intro m hm
    have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hmu
    have hmm : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hmu
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have hab' : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hab']
      exact add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hmm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galEmbFam :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime],
      (∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A ∧ (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A) ∧
      Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l = shaFam E Ω l ∧ (cycZ k Ω l).comp (galEmb k E Ω) = cycZ E Ω l ∧
      ∀ e : ℤ, (LDataCardLeFinrank.qzG k Ω l e).comp (galEmb k E Ω) = LDataCardLeFinrank.qzG E Ω l e := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hD : ∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
    exact Iff.rfl
  have hI : ∀ A : ValuationSubring Ω, (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl
  refine ⟨fun A => ⟨hD A, hI A⟩, ?_, ?_, fun e => ?_⟩
  · ext D
    constructor
    · rintro ⟨D', ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩
      · exact Or.inl ⟨A, hl, hD A⟩
      · exact Or.inr ⟨A, hI A⟩
    · rintro (⟨A, hl, rfl⟩ | ⟨A, rfl⟩)
      · exact ⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩
      · exact ⟨_, Or.inr ⟨A, rfl⟩, hI A⟩
  · exact MonoidHom.ext fun _ => rfl
  · exact MonoidHom.ext fun _ => rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)

theorem UpperTheory.V.Base.galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω
  intros
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _
    constructor
    · rintro h y ⟨x, rfl⟩
      simpa using h x
    · intro h x
      simpa using h _ ⟨x, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩,
        fun σ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩
  · intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  · rw [hset]
    exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galQuot :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E],
      Function.Surjective (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)) ∧
      (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)).ker = galOf k E Ω ∧
      ∀ σ : G k Ω, IsLift (AlgEquiv.restrictNormalHom E σ : E ≃ₐ[k] E).toRingEquiv σ.toRingEquiv := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Normal k Ω := IsAlgClosure.normal k Ω
  have hc : ∀ (σ : G k Ω) (x : E),
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) := by
    intro σ x
    exact (AlgEquiv.restrictNormal_commutes σ E x).symm
  refine ⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, ?_⟩
  · ext σ
    rw [MonoidHom.mem_ker]
    change _ ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x
    constructor
    · intro h x
      rw [hc, h]
      rfl
    · intro h
      ext x
      apply (algebraMap E Ω).injective
      rw [← hc, h]
      rfl
  · intro σ x
    exact hc σ x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflAct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.inflAct :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv →
      ∀ x y, Infl k D e x y → Infl k D e (galoisActionOnCohomology D e τ x) (conjRep (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ y) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ D e τ σ h x y hxy
  obtain ⟨z, z', rfl, rfl, hz⟩ := hxy
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ z'
  refine ⟨z₁, z₂, by rw [galois_action_cohomology_eq_conj D e h, e₁], by rw [conjRep_apply, e₂], fun g => ?_⟩
  have hc : conjHom (galOf k E Ω) σ ⟨galEmb k E Ω g, galEmb_mem k E Ω g⟩ =
      ⟨galEmb k E Ω (conjGal h g), galEmb_mem k E Ω _⟩ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  rw [f₂, f₁, conjGS_toGS, hc, hz]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

theorem UpperTheory.V.Base.normO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 →
      ‖(a : PadicAlgCl l)‖ ^ (eO l O).toNat = ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  intro l _ O _ _ a ha
  have hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)
  have hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg ((u : O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : ((l : O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : eO l O = IsDiscreteValuationRing.addVal O (l : O) := Ring.ord_eq_addVal (l : O)
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.places :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
      (A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v) ∧ (A = ⊤ → Ine (F := k) A = ⊥ ∧ ¬ A.valuation (l : Ω) < 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v → (A.valuation (l : Ω) < 1 ↔ v ∈ Above (F := k) l)) ∧
      (¬ A.valuation (l : Ω) < 1 → Ine (F := k) A ≤ (cycZ k Ω l).ker) := by
  intro k Ω _ _ _ _ _ l _ A
  have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := by
    intro z hz
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
    exact A.valuation_le_one y
  have hOk : ∀ x : 𝓞 k, A.valuation (algebraMap k Ω (x : k)) ≤ 1 := fun x =>
    hint _ x.isIntegral_coe.algebraMap
  have hl1 : A.valuation (l : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A l)
  have htop : A = ⊤ → ∀ y : Ω, A.valuation y < 1 → y = 0 := by
    intro hA y hy
    by_contra h0
    have h2 : A.valuation y⁻¹ ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _)
    have h3 : A.valuation y * A.valuation y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    have h4 : A.valuation y * A.valuation y⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hy
    exact absurd h3 (ne_of_lt h4)
  have hlne : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hA
    let p : Ideal (𝓞 k) :=
      { carrier := {x | A.valuation (algebraMap k Ω (x : k)) < 1}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_add (f := _)] at *
          exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
        zero_mem' := by simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hOk c)) hx }
    have hprime : p.IsPrime := by
      refine ⟨?_, ?_⟩
      · rw [Ne, Ideal.eq_top_iff_one]
        show ¬ A.valuation (algebraMap k Ω ((1 : 𝓞 k) : k)) < 1
        simp
      · intro x y hxy
        change A.valuation (algebraMap k Ω ((x * y : 𝓞 k) : k)) < 1 at hxy
        change A.valuation (algebraMap k Ω (x : k)) < 1 ∨ A.valuation (algebraMap k Ω (y : k)) < 1
        simp only [map_mul] at hxy
        by_contra h
        push_neg at h
        have hx1 : A.valuation (algebraMap k Ω (x : k)) = 1 := le_antisymm (hOk x) h.1
        have hy1 : A.valuation (algebraMap k Ω (y : k)) = 1 := le_antisymm (hOk y) h.2
        rw [hx1, hy1, one_mul] at hxy
        exact lt_irrefl _ hxy
    have hne : p ≠ ⊥ := by
      intro hbot
      apply hA
      have hk : ∀ y : k, A.valuation (algebraMap k Ω y) ≤ 1 := by
        intro y
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 k) y
        have hb0 : (b : 𝓞 k) ≠ 0 := nonZeroDivisors.ne_zero hb
        have hbv : A.valuation (algebraMap k Ω (algebraMap (𝓞 k) k b)) = 1 := by
          refine le_antisymm (hOk b) (not_lt.mp fun h => hb0 ?_)
          have hbp : b ∈ p := h
          rw [hbot] at hbp
          exact (Submodule.mem_bot _).mp hbp
        rw [map_div₀, map_div₀, hbv, div_one]
        exact hOk a
      have hf : ∀ y : k, algebraMap k Ω y ∈ A := fun y => (A.valuation_le_one_iff _).mp (hk y)
      let f : k →+* A := (algebraMap k Ω).codRestrict A hf
      have hcomp : (algebraMap A Ω).comp f = algebraMap k Ω := by
        ext y
        rfl
      rw [eq_top_iff]
      intro z _
      have hz : IsIntegral A z := by
        obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := k) z
        refine ⟨q.map f, hqm.map f, ?_⟩
        rw [Polynomial.eval₂_map, hcomp]
        exact hq
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hz
      exact y.2
    exact ⟨⟨p, hprime, hne⟩, fun x => Iff.rfl⟩
  · intro hA
    refine ⟨?_, fun h => hlne (htop hA _ h)⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨-, hσ⟩ := hσ
    ext z
    have h1 := hσ z ((A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _))
    have h2 := htop hA _ h1
    rw [sub_eq_zero] at h2
    simpa using h2
  · intro v hv
    have h := hv (l : 𝓞 k)
    simp only [map_natCast] at h
    exact h
  · intro hl σ hσ
    obtain ⟨-, hσ⟩ := hσ
    have hl1' : A.valuation (l : Ω) = 1 := le_antisymm hl1 (not_lt.mp hl)
    have hfix : ∀ (n : ℕ) (t : Ω), t ^ (l ^ n) = 1 → σ t = t := by
      intro n t ht
      have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
      set N := l ^ n with hNdef
      have htI : IsIntegral ℤ t := IsIntegral.of_pow hN (by rw [ht]; exact isIntegral_one)
      have huN : (σ t) ^ N = 1 := by rw [← map_pow, ht, map_one]
      have huI : IsIntegral ℤ (σ t) := IsIntegral.of_pow hN (by rw [huN]; exact isIntegral_one)
      by_contra hne
      set u := σ t with hu
      set s := t ^ (N - 1) with hs
      have hst : s * t = 1 := by rw [hs, ← pow_succ, Nat.sub_add_cancel hN, ht]
      set w := u * s with hw
      have hwN : w ^ N = 1 := by
        rw [hw, mul_pow, huN, one_mul, hs, ← pow_mul, mul_comm (N - 1) N, pow_mul, ht, one_pow]
      have hw1 : w ≠ 1 := by
        intro h
        apply hne
        have h' : w * t = t := by rw [h, one_mul]
        rw [hw, mul_assoc, hst, mul_one] at h'
        exact h'
      have hsI : IsIntegral ℤ s := htI.pow _
      have hwI : IsIntegral ℤ w := huI.mul hsI
      have hval : A.valuation (w - 1) < 1 := by
        have hws : w - 1 = (u - t) * s := by rw [hw, sub_mul, mul_comm t s, hst]
        rw [hws, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint s hsI)) (hσ t (hint t htI))
      set c := ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, w ^ i with hc
      have hcI : IsIntegral ℤ c :=
        IsIntegral.sum _ fun j _ => IsIntegral.sum _ fun i _ => hwI.pow i
      have hid : (N : Ω) = (1 - w) * c := by
        rw [hc, Finset.mul_sum]
        simp_rw [mul_neg_geom_sum]
        rw [Finset.sum_sub_distrib, geom_sum_eq hw1, hwN, sub_self, zero_div, sub_zero]
        simp
      have hNv : A.valuation (N : Ω) = 1 := by
        rw [hNdef, Nat.cast_pow, map_pow, hl1', one_pow]
      have hlt : A.valuation (N : Ω) < 1 := by
        rw [hid, map_mul, Valuation.map_sub_swap]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint c hcI)) hval
      rw [hNv] at hlt
      exact lt_irrefl _ hlt
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    rw [MonoidHom.mem_ker]
    change cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G k Ω) Ω σ) = 1
    apply Units.ext
    rw [Units.val_one]
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_one]
    refine (modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ (l ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ht, Units.val_one]
    change σ (t : Ω) = _
    rw [hfix n _ ht']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp at ht'
      simp [ht']
    · haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
      rw [ZMod.val_one, pow_one]
end

