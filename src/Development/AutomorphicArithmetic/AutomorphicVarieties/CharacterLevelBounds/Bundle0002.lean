module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.levGal :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → IsAbelianGalois ℚ E ∧ Module.finrank ℚ E = H.index ∧
          ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω], galOf ℚ E Ω = levH ℚ Ω H ∧ (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := by
  intro E _ _ N _ H hlev
  obtain ⟨j, ζ, hζ, hj⟩ := hlev
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H := by
    ext u
    unfold KStar.TotallyRealRoots.fieldSubgroup
    rw [Subgroup.mem_map_equiv]
    set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef
    have hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u := by
      rw [hτdef]
      exact MulEquiv.apply_symm_apply _ u
    have hτ : τ ζ = ζ ^ (u : ZMod N).val := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]
    rw [← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (j x) ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩
      exact h x
  have hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E := by
    rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    rfl
  have hfin : Module.finrank ℚ E = H.index := by
    rw [← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]
    unfold KStar.TotallyRealRoots.fieldSubgroup
    exact (Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm
  refine ⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩
  intro Ω _ _ _ _
  haveI : IsScalarTower ℚ E Ω := inferInstance
  haveI : IsAlgClosure E Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  have heq : galOf ℚ E Ω = levH ℚ Ω H := by
    ext σ
    rw [mem_galOf]
    unfold levH
    rw [Subgroup.mem_comap, ← hfs]
    exact LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ)
      (fun z hz => cls_spec N σ z hz)
  obtain ⟨-, hopen, hidx⟩ := galEmbTop ℚ E Ω
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hidx, hfin]
  · rw [← heq]
    exact hopen
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr
open scoped Pointwise

namespace UpperTheory.V.Chr.RationalPlaces

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv ((l : ℕ) : 𝓞 ℚ) = (l : ℤ) := map_natCast _ l
  rw [← e] at h
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)).mp h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  unfold IsPlaceOver
  intro x
  set m : ℤ := Rat.ringOfIntegersEquiv x with hmdef
  have hx : algebraMap ℚ Ω (x : ℚ) = (m : Ω) := by
    have e : ((m : ℤ) : ℚ) = (x : ℚ) := by
      rw [hmdef, Rat.ringOfIntegersEquiv_apply_coe]
    rw [← e, map_intCast]
  have hmem : x ∈ (vQ l).asIdeal ↔ (l : ℤ) ∣ m := by
    change x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  have hA' : A.valuation ((l : ℤ) : Ω) < 1 := by
    rw [Int.cast_natCast]
    exact hA
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k =>
    (ValuationSubring.valuation_le_one_iff A _).mpr (intCast_mem A k)
  rw [hx, hmem]
  constructor
  · intro hm
    by_contra hnd
    have hirr : Irreducible (l : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).mpr hnd
    have h1 : ((a : Ω) * (l : ℤ) + (b : Ω) * (m : Ω)) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) hab
      push_cast at this ⊢
      exact this
    have hle : A.valuation (1 : Ω) < 1 := by
      rw [← h1]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hA'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hm
    rw [map_one] at hle
    exact lt_irrefl _ hle
  · rintro ⟨k, hk⟩
    rw [hk, Int.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint k)) hA'

private theorem val_natCast_le_one (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

private theorem val_lt_one_iff (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) :
    A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1 := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp
  | prime p hp =>
    intro _
    rw [hp.primeFactors]
    simp
  | mul a b iha ihb =>
    intro hab
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have key : A.valuation (a : Ω) * A.valuation (b : Ω) < 1 ↔
        A.valuation (a : Ω) < 1 ∨ A.valuation (b : Ω) < 1 := by
      constructor
      · intro h
        by_contra hc
        push_neg at hc
        have e1 : A.valuation (a : Ω) = 1 := le_antisymm (val_natCast_le_one A a) hc.1
        have e2 : A.valuation (b : Ω) = 1 := le_antisymm (val_natCast_le_one A b) hc.2
        rw [e1, e2, one_mul] at h
        exact lt_irrefl _ h
      · rintro (h | h)
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_natCast_le_one A b)) h
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_natCast_le_one A a)) h
    rw [Nat.cast_mul, map_mul, Nat.primeFactors_mul ha hb, key, iha ha, ihb hb]
    simp only [Finset.mem_union]
    constructor
    · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
      exacts [⟨p, Or.inl hp, h⟩, ⟨p, Or.inr hp, h⟩]
    · rintro ⟨p, hp | hp, h⟩
      exacts [Or.inl ⟨p, hp, h⟩, Or.inr ⟨p, hp, h⟩]

private theorem exists_place [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let x : (⊥ : Subring Ω) := ⟨(p : Ω), natCast_mem _ p⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨m, hm⟩ := Subring.mem_bot.mp y.2
    have h1 : (((p : ℤ) * m : ℤ) : Ω) = ((1 : ℤ) : Ω) := by
      have hv := congrArg Subtype.val hy
      push_cast
      rw [hm]
      exact hv
    have h2 : (p : ℤ) * m = 1 := Int.cast_injective h1
    have h3 : IsUnit (p : ℤ) := isUnit_iff_exists_inv.mpr ⟨m, h2⟩
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h3
    exact hp.ne_one h3
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

end UpperTheory.V.Chr.RationalPlaces

open UpperTheory.V.Chr.RationalPlaces in
theorem UpperTheory.V.Chr.placesQ :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω], (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
          (∀ (A : ValuationSubring Ω) (n : ℕ), n ≠ 0 → (A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1)) ∧
          ∀ (p : ℕ) (A A' : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 →
            ∃ u : G ℚ Ω, (∀ x ∈ Dec (F := ℚ) A, u⁻¹ * x * u ∈ Dec (F := ℚ) A') ∧ ∀ x ∈ Ine (F := ℚ) A, u⁻¹ * x * u ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _
  refine ⟨fun p hp => exists_place p hp, fun A n hn => val_lt_one_iff A n hn, ?_⟩
  intro p A A' hp hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
  have hL : IsLift (RingEquiv.refl ℚ) (σ⁻¹ : G ℚ Ω).toRingEquiv := fun x =>
    AlgEquiv.commutes _ x
  have hmem : ∀ x : Ω, (σ⁻¹ : G ℚ Ω).toRingEquiv x ∈ A ↔ x ∈ A' := by
    intro x
    rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hconj : ∀ g : G ℚ Ω, (σ⁻¹)⁻¹ * g * σ⁻¹ = conjGal hL g := by
    intro g
    ext x
    rfl
  refine ⟨σ⁻¹, ?_, ?_⟩
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Dec hL hmem hg
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Ine hL hmem hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (h : ζ ^ n = 1) (h1 : ζ ≠ 1) :
    ζ - 1 ∣ (n : O) := by
  have hS : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have hg := mul_geom_sum ζ n
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)
  have hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  rw [hn]
  apply Finset.dvd_sum
  intro i _
  have hd := sub_dvd_pow_sub_pow ζ 1 i
  rw [one_pow] at hd
  rw [← neg_sub (ζ ^ i) 1]
  exact (dvd_neg).mpr hd

theorem UpperTheory.V.Chr.rootVal :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (n : ℕ), n ≠ 0 → IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O ∧
          (∀ ζ : O, ζ ^ n = 1 → ζ ≠ 1 → IsDiscreteValuationRing.addVal O (ζ - 1) ≤ (n.factorization l : ℕ∞) * eO l O) ∧ eO l O ≠ ⊤ ∧ CharZero O := by
  intro l _ O _ _ _ _ _ n hn
  obtain ⟨hiO, -, -, -, -, -, -, hvO, hunit⟩ := dvrFacts l O
  have hp : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O := by
    have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O) := hunit _ (Nat.not_dvd_ordCompl hp hn)
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]
    rw [Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu,
      add_zero, hvO, nsmul_eq_mul]
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro ζ hζ h1
    rw [← hval]
    exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)
  · rw [hvO]
    exact fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  · exact charZero_of_injective_algebraMap hiO
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SelFam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem selFam_length_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.subtype_injective _)
    f.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective _ (Submodule.subtype_injective _))

private theorem selFam_abs {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {ι : Type} [Fintype ι]
    {Y Z : ι → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)]
    (A B : Submodule R X) (p : ∀ i, X →ₗ[R] Y i) (q : ∀ i, Y i →ₗ[R] Z i)
    (h1 : ∀ i, ∀ x ∈ A, q i (p i x) = 0) (h2 : ∀ x ∈ A, (∀ i, p i x = 0) → x ∈ B) :
    Module.length R A ≤ Module.length R B + ∑ i, Module.length R (LinearMap.ker (q i)) := by
  let f : A →ₗ[R] (∀ i, LinearMap.ker (q i)) :=
    LinearMap.pi fun i => LinearMap.codRestrict _ ((p i).comp A.subtype) (fun x => h1 i x.1 x.2)
  have hk : ∀ x : LinearMap.ker f, (A.subtype.comp (LinearMap.ker f).subtype) x ∈ B := fun x =>
    h2 x.1.1 x.1.2 fun i => congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 x.2) i)
  have := selFam_length_le f (LinearMap.codRestrict _ _ hk) (by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1))
  rwa [Module.length_pi_of_fintype] at this

private theorem selFam_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U D D' : Subgroup G) (u : G) (hu : u ∈ U) (hux : ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D) (z : Z1U ρ U)
    (hi : resU ρ (inf_le_left : U ⊓ D ≤ U) (Submodule.Quotient.mk z) = 0) :
    ∃ m, ∀ x : U, x.1 ∈ D' → z.1 x = ρ x m - m := by
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ _ z).1 hi
  refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun x hx => ?_⟩
  have hy : u⁻¹ * x.1 * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) x.2) hu
  have h1 : z.1 ⟨u⁻¹ * x.1 * u, hy⟩ = ρ (u⁻¹ * x.1 * u) m - m := hm ⟨_, hy, hux x.1 ⟨x.2, hx⟩⟩
  have e1 : (⟨u, hu⟩ : U) * ⟨_, hy⟩ = x * ⟨u, hu⟩ := Subtype.ext (by simp [mul_assoc])
  have e2 := congrArg z.1 e1
  rw [z.2.2, z.2.2] at e2
  have e3 : z.1 ⟨u, hu⟩ + ρ u (z.1 ⟨_, hy⟩) = z.1 x + ρ x (z.1 ⟨u, hu⟩) := e2
  have e4 : ρ u (ρ (u⁻¹ * x.1 * u) m) = ρ x (ρ u m) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [h1, map_sub, e4] at e3
  rw [eq_sub_of_add_eq e3.symm, map_sub]
  abel

theorem UpperTheory.V.Chr.selFam :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
          [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U : Subgroup G) (𝒟 𝒟' : Set (Subgroup G)) (ι : Type) [Fintype ι] (I D : ι → Subgroup G) (h : ∀ i, I i ≤ D i),
          (∀ i, I i ∈ 𝒟) → (∀ D' ∈ 𝒟', D' ∈ 𝒟 ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
          Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U 𝒟') +
            ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_left U (h i)))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U 𝒟 𝒟' ι _ I D h hI hc
  refine selFam_abs (LocSel ρ U 𝒟) (LocSel ρ U 𝒟') (fun i => resU ρ (inf_le_left : U ⊓ D i ≤ U))
    (fun i => resU ρ (inf_le_inf_left U (h i))) (fun i x hx => ?_) (fun x hx hi => ?_)
  · exact (resU_resU ρ _ _ x).trans (mem_locSel.1 hx (I i) (hI i))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine mk_mem_locSel.2 fun D' hD' => ?_
    rcases hc D' hD' with hle | ⟨i, u, hu, hux⟩
    · exact mk_mem_locSel.1 hx D' hle
    · exact selFam_conj ρ U (D i) D' u hu hux z (hi i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SumBack
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sumBack_one {ι : Type} (S : Finset ι) (f : ι → ℕ∞) (a : ℕ∞) (b E : ℕ) (hE : E ≠ 0)
    (hf : ∀ i ∈ S, f i ≠ ⊤) (h : a * (E : ℕ∞) ≤ ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞))) :
    a ≠ ⊤ ∧ (a.toNat : ℝ) ≤ ∑ i ∈ S, ((f i).toNat : ℝ) / (E : ℝ) + S.card * (b : ℝ) := by
  have hsum : ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞)) = ((∑ i ∈ S, ((f i).toNat + b * E) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    push_cast
    rw [ENat.coe_toNat (hf i hi)]
  rw [hsum] at h
  have ha : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (by exact_mod_cast hE)] at h
    exact absurd h (not_le.2 (ENat.coe_lt_top _))
  refine ⟨ha, ?_⟩
  have h2 : a.toNat * E ≤ ∑ i ∈ S, ((f i).toNat + b * E) := by
    rw [← ENat.coe_toNat ha] at h
    exact_mod_cast h
  have hE' : (0 : ℝ) < E := by exact_mod_cast Nat.pos_of_ne_zero hE
  have h3 : (a.toNat : ℝ) * E ≤ ∑ i ∈ S, (((f i).toNat : ℝ) + b * E) := by exact_mod_cast h2
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h3
  rw [← Finset.sum_div]
  have h4 : (∑ i ∈ S, ((f i).toNat : ℝ)) / E + S.card * (b : ℝ) = ((∑ i ∈ S, ((f i).toNat : ℝ)) + S.card * ((b : ℝ) * E)) / E := by
    field_simp
  rw [h4, le_div_iff₀ hE']
  exact h3

theorem UpperTheory.V.Chr.sumBack :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) (T : ℕ → Finset ι) (T₀ : Finset ι) (f : ι → ℕ → ℕ∞) (a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ),
          (∀ e, T e ⊆ T₀) → (∀ e, 0 < e → e < t → (∀ i ∈ T e, f i e ≠ ⊤) ∧ a e * eO l O ≤ ∑ i ∈ T e, (f i e + (b e : ℕ∞) * eO l O)) →
          (∀ e, 0 < e → e < t → a e ≠ ⊤) ∧
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, nrm l O (f i e) + T₀.card * ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) := by
  intro l _ O _ _ _ _ _ ι T T₀ f a b t hT h
  obtain ⟨-, -, -, -, -, hne, hle, -, -⟩ := dvrFacts l O
  have htop : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  have hEO : eO l O = (((eO l O).toNat : ℕ) : ℕ∞) := (ENat.coe_toNat htop).symm
  have hE : (eO l O).toNat ≠ 0 := by
    intro h0
    apply hne
    rw [hEO, h0]
    rfl
  have key : ∀ e ∈ Finset.Ico 1 t, a e ≠ ⊤ ∧ ((a e).toNat : ℝ) ≤ ∑ i ∈ T e, ((f i e).toNat : ℝ) / ((eO l O).toNat : ℝ) + (T e).card * (b e : ℝ) := by
    intro e he
    rw [Finset.mem_Ico] at he
    obtain ⟨h1, h2⟩ := h e (by omega) he.2
    rw [hEO] at h2
    exact sumBack_one (T e) (fun i => f i e) (a e) (b e) _ hE h1 h2
  refine ⟨fun e he0 het => (key e (Finset.mem_Ico.2 ⟨he0, het⟩)).1, ?_⟩
  have hn : ∀ x, nrm l O x = (x.toNat : ℝ) / ((eO l O).toNat : ℝ) := fun x => rfl
  simp only [hn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => (key e he).2.trans ?_
  gcongr
  exact hT e
end

