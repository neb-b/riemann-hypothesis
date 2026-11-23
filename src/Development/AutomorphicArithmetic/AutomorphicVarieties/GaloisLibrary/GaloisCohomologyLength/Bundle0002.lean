module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ContScal
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.contScal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* ℤ_[l]ˣ), (Continuous fun g => ((ψ g : ℤ_[l]ˣ) : ℤ_[l])) → ContAction (scalRep (QZ l) ψ) := by
  intro l _ Γ _ _ ψ hψ
  haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  apply continuous_prod_of_discrete_right.mpr
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  let q : ℚ_[l] → QZ l := fun z => Submodule.Quotient.mk z
  have hmk : Continuous q := by
    refine (continuous_discrete_rng (β := QZ l)).mpr ?_
    intro b
    obtain ⟨y, rfl⟩ : ∃ y, q y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
    have e : q ⁻¹' {q y} = Metric.closedBall y 1 := by
      ext z
      have h1 : q z = q y ↔ z - y ∈ ZlSub l := Submodule.Quotient.eq (ZlSub l)
      rw [Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range,
        Metric.mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hw]
        exact w.norm_le_one
      · intro h
        exact ⟨⟨z - y, h⟩, rfl⟩
    rw [e]
    exact IsUltrametricDist.isOpen_closedBall y one_ne_zero
  have hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x :=
    (continuous_subtype_val.comp hψ).mul continuous_const
  refine (hmk.comp hc).congr ?_
  intro g
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.decActRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ g ∈ Dec (F := F) A, ∃ k : ℕ, ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l ^ k := by
  intro F Ω _ _ _ _ _ l _ A hA m hm g hg
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    exact hl.one_lt.ne' hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A := by
    intro ξ hξ
    rw [← ValuationSubring.valuation_le_one_iff]
    exact (pow_le_one_iff hm0).mp (by rw [← map_pow, hξ, map_one])
  have hgm : (g ζ0) ^ m = 1 := by rw [← map_pow, hζ0.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ0.eq_pow_of_pow_eq_one hgm
  let g' : A.decompositionSubgroup F := ⟨g, hg⟩
  have hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  let z0 : A := ⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩
  let ω : IsLocalRing.ResidueField A := IsLocalRing.residue A z0
  have hσω : g' • ω = ω ^ a := by
    have hz : g' • z0 = z0 ^ a := Subtype.ext (by
      change g ζ0 = ζ0 ^ a
      exact ha.symm)
    simp only [ω]
    rw [← IsLocalRing.ResidueField.residue_smul, hz, map_pow]
  let σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with
      commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod
        ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp
          (algebraMap (ZMod l) (IsLocalRing.ResidueField A)))
        (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) r }
  have hσ : ∀ x, σ x = g' • x := fun x => rfl
  let E := IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))
  have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have hint : IsIntegral (ZMod l) ω := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_
    have h1 : ω ^ m = 1 := by
      simp only [ω]
      rw [← map_pow]
      have : z0 ^ m = 1 := Subtype.ext (by
        change ζ0 ^ m = 1
        exact hζ0.pow_eq_one)
      rw [this, map_one]
    rw [h1]
    exact isIntegral_one
  haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod l)
  have hEle : E ≤ IntermediateField.comap σ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    show σ ω ∈ E
    rw [hσ, hσω]
    exact pow_mem hωE a
  have hmapE : ∀ x ∈ E, σ x ∈ E := fun x hx => hEle hx
  let τ : E →ₐ[ZMod l] E :=
    { toFun := fun x => ⟨σ x, hmapE x.1 x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1)
      commutes' := fun r => Subtype.ext (σ.commutes r) }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ
  have hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ)) := by
    rw [← hn]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hres : ω ^ a = ω ^ (l ^ (n : ℕ)) := by
    have h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω := rfl
    have := congrArg Subtype.val hτω
    rw [h2] at this
    rw [← hσω, ← hσ]
    simpa using this
  have hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ)) := by
    rw [← ha]
    have hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    have hroota : (ζ0 ^ a) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    refine (UpperTheory.V.LDataCardLeFinrank.ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_
    have hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]
      exact hres
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    simpa using hsub
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecFrob
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

namespace UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl.out

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span _ ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact intCast_mem A n

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hn
    have hirr : Irreducible ((l : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hn
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) (by exact_mod_cast hA)
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) (by exact_mod_cast hA)

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]
  simp

end UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

open UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius in
theorem UpperTheory.V.LDataCardLeFinrank.decFrob :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, ∀ m : ℕ, m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l := by
  intro Ω _ _ _ l _ A hA
  have hP : IsPlaceOver (F := ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hP
  rw [normV_vQ] at hσ
  refine ⟨σ, hσD, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (by simpa using hm)
  have hζv : A.valuation ζ ≤ 1 := by
    by_contra h
    have h2 := one_lt_pow' (not_le.mp h) hm0
    rw [← map_pow, hζ, map_one] at h2
    exact lt_irrefl _ h2
  have key := (ineFixRoots ℚ Ω l A hA m hm (ζ ^ l) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1
  apply key (σ ζ)
  · rw [← map_pow, hζ, map_one]
  · exact hσ ζ hζv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.galTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∃ φ : G F' Ω' →* G F Ω, Continuous φ ∧ (∀ g x, σ (φ g x) = g (σ x)) ∧ (∀ (l : ℕ) [Fact l.Prime] (g : G F' Ω'), cycZ F Ω l (φ g) = cycZ F' Ω' l g) ∧ Function.Injective φ ∧ (Function.Surjective f → Function.Surjective φ) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ hσ
  have hc : ∀ g : G F' Ω', ∀ x : F,
      ((σ.trans g.toRingEquiv).trans σ.symm) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro g x
    simp only [RingEquiv.trans_apply, hσ, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    rw [← hσ, RingEquiv.symm_apply_apply]
  let φ : G F' Ω' →* G F Ω :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (hc g)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hφ : ∀ g x, φ g x = σ.symm (g (σ x)) := fun _ _ => rfl
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  refine ⟨φ, ?_, fun g x => by rw [hφ, σ.apply_symm_apply], ?_, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro U hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    let b := Module.finBasis F E
    have hV : (⋂ i, {g : G F' Ω' | g (σ (b i)) = σ (b i)}) ∈ nhds (1 : G F' Ω') :=
      Filter.iInter_mem.2 fun i =>
        IsOpen.mem_nhds (isOpen_setOf_apply (σ (b i)) (fun y => y = σ (b i))) rfl
    refine Filter.mem_of_superset hV ?_
    intro g hg
    apply hEU
    have hb : ∀ i, φ g (b i) = b i := by
      intro i
      rw [hφ, Set.mem_iInter.1 hg i, RingEquiv.symm_apply_apply]
    show φ g ∈ fixingSubgroup (G F Ω) (E : Set Ω)
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [AlgEquiv.smul_def]
    have hs := congrArg (fun z : E => (z : Ω)) (b.sum_repr ⟨y, hy⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hs
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hs, map_sum]
    simp [map_smul, hb]
  · intro l _ g
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap F' Ω').injective
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed F'
    simp only [cycZ, MonoidHom.comp_apply]
    refine (KStar.TotallyRealRoots.cyclotomicCharacter_conj σ _ _ fun x => ?_).symm
    show g (σ x) = σ (φ g x)
    rw [hφ, σ.apply_symm_apply]
  · intro a b h
    ext y
    have := congrArg (fun k : G F Ω => k (σ.symm y)) h
    simpa [hφ] using this
  · intro hf h
    have hc' : ∀ y : F', ((σ.symm.trans h.toRingEquiv).trans σ) (algebraMap F' Ω' y) =
        algebraMap F' Ω' y := by
      intro y
      obtain ⟨x, rfl⟩ := hf y
      rw [← hσ]
      simp
    exact ⟨AlgEquiv.ofRingEquiv hc', by ext x; simp [hφ]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneOpen
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.ineOpen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    v ∈ Above (F := F) l → IsPlaceOver A v →
    IsOpen (ineImage F l A : Set ℤ_[l]ˣ) ∧ (ineImage F l A).index ≠ 0 ∧
    (ineImage F l A).index ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l _ v A hl hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hl' : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := hl
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl'
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have hK : Module.finrank ℚ F = K.fixingSubgroup.index := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finrank_eq
  have hK0 : K.fixingSubgroup.index ≠ 0 := by
    rw [← hK]; exact Module.finrank_pos.ne'
  let I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A
  let f : I →* ℤ_[l]ˣ := (cycZ (F := ℚ) (Ω := Ω) l).comp I.subtype
  have hf : Function.Surjective f := fun u => by
    obtain ⟨σ, hσ, h⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
    exact ⟨⟨σ, hσ⟩, h⟩
  have hle : (K.fixingSubgroup.subgroupOf I).map f ≤ ineImage F l A := by
    rintro _ ⟨σ, hσ, rfl⟩
    have hmem : σ.1 ∈ K.fixingSubgroup := hσ
    let g : G F Ω := { σ.1.toRingEquiv with
      commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
    exact ⟨g, σ.2, rfl⟩
  have hrel0 : K.fixingSubgroup.relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  have hrel : K.fixingSubgroup.relIndex I ≤ K.fixingSubgroup.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top hrel0
  have hrelI : K.fixingSubgroup.relIndex I ≠ 0 := fun h =>
    hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
  have hdvd : (ineImage F l A).index ∣ K.fixingSubgroup.relIndex I :=
    (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)
  have h0 : (ineImage F l A).index ≠ 0 := ne_zero_of_dvd_ne_zero hrelI hdvd
  refine ⟨?_, h0, ?_⟩
  · have : (ineImage F l A).FiniteIndex := ⟨h0⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    exact ((isClosed_Ine (F := F) A).isCompact.image (continuous_cycZ F Ω l)).isClosed
  · rw [hK]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hrelI) hdvd).trans hrel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.levelLeIne :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
      v ∈ Above (F := F) l → IsPlaceOver A v →
      KStar.TotallyRealRoots.levelGroup l N (KStar.TotallyRealRoots.fieldSubgroup N K φ.fieldRange ⊓ KStar.TotallyRealRoots.levelInertia l N) ≤
        UpperTheory.V.LDataCardLeFinrank.ineImage F l A := by
  intro F Ω _ _ _ _ _ N _ K _ _ _ φ l _ v A hv hA u hu
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨h, ⟨hF, hI⟩, hh⟩ := KStar.TotallyRealRoots.mem_levelGroup.mp hu
  have hl : A.valuation (l : Ω) < 1 := by
    have := (hA (l : 𝓞 F)).mpr hv
    simpa using this
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hl u
  have hcop : (N / l ^ N.factorization l).Coprime l :=
    (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)).symm
  have hpos : 0 < N / l ^ N.factorization l := Nat.ordCompl_pos l (NeZero.ne N)
  have hfixm : ∀ ζ : Ω, ζ ^ (N / l ^ N.factorization l) = 1 → σ ζ = ζ := fun ζ hζ =>
    (ineFixRoots ℚ Ω l A hl _ hcop ζ hζ).2 σ hσI
  have hroots : ∀ ζ : Ω, ζ ^ N = 1 → σ.toRingEquiv ζ = ζ ^ (h : ZMod N).val := by
    rw [classIff Ω l N σ.toRingEquiv h]
    refine ⟨fun ζ hζ => ?_, ?_⟩
    · have h1 : (ZMod.unitsMap (Nat.ordCompl_dvd N l)) h = 1 := hI
      have e : σ.toRingEquiv ζ = ζ := hfixm ζ hζ
      rw [e, h1, Units.val_one]
      rcases Nat.lt_or_ge 1 (N / l ^ N.factorization l) with hm | hm
      · haveI : Fact (1 < N / l ^ N.factorization l) := ⟨hm⟩
        rw [ZMod.val_one, pow_one]
      · have hm1 : N / l ^ N.factorization l = 1 := by omega
        rw [hm1, pow_one] at hζ
        rw [hζ, one_pow]
    · rw [hh]
      congr 1
      exact hσu.symm
  have hfixF : ∀ x : F, σ.toRingEquiv (algebraMap F Ω x) = algebraMap F Ω x :=
    (classFix F Ω N K φ σ.toRingEquiv h hroots).mpr hF
  let τ : Ω ≃ₐ[F] Ω := { σ.toRingEquiv with commutes' := hfixF }
  refine ⟨τ, ⟨?_, fun x hx => hσI.2 x hx⟩, ?_⟩
  · exact hσI.1
  · rw [← hσu]
    rfl
end

