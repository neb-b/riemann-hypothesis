module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardGlobalCocyclesLeOfIwasawaRank
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_fin (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : N ≠ 0) : (plDvd F N).Finite := by
  have h : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Ws.card_globalCocycles_le_of_iwasawaRank :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N r g : ℕ), l ≠ 2 → N ≠ 0 → l ∣ N → (plDvd F N).ncard ≤ g → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → K.Normal → IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index → (∀ σ ∈ K, ∀ m, ρ σ m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g + Module.finrank ℚ F)) ∧ (IsTotallyReal F → (∀ σ : G F Ω, IsCC σ → ∀ m, ρ σ m = m) → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g))) := by
  intro P F Ω _ _ _ _ _ l _ R M _ _ _ _ hlM ρ K N r g hl hN hlN hg hI hKn hKo hKi hKρ hKc hX
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (G F Ω) R M hlM ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hfin := plDvd_fin F N hN
  have hcard : hfin.toFinset.card ≤ g := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
  have hmem : ∀ v, v ∈ plDvd F N → v ∈ hfin.toFinset := fun v hv => hfin.mem_toFinset.2 hv
  generalize hfin.toFinset = S at hcard hmem
  have hS : ContainsAbove S l := fun v hv => hmem v (by
    obtain ⟨k, rfl⟩ := hlN
    show ((l * k : ℕ) : 𝓞 F) ∈ v.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv)
  obtain ⟨ρS, h1, h2, h3⟩ := exists_descent_to_galoisGroupUnramifiedOutside F Ω (ZMod (l ^ 1)) M S ρ' K N hmem
    (fun σ h m => by rw [hρ', hI σ h]) hKo (fun σ h m => by rw [hρ', hKρ σ h])
  have hc : ∀ w : InfinitePlace F, ∃ c : G F Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · obtain ⟨c, hc⟩ := exists_complexConjugation_at_realPlace F Ω w hw
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose c hc using hc
  obtain ⟨hZ, hb⟩ := greenberg_wiles_count_mod_l P F Ω l M S ρS K r c hl hS h2 hKn hKi
    (fun σ h m => by rw [h1, hρ', hKρ σ h]) hKc hX hc
  have hM : 0 < Nat.card M := Nat.card_pos
  have hex : ∀ z : cocOff ρ (ineOff F Ω N), ∃ y : Z1 ρS, ∀ g, y.1 (toGS Ω _ g) = z.1 g := fun z => by
    obtain ⟨y, hy, e⟩ := h3 z.1 ⟨z.2.1, fun a b => by rw [hρ']; exact z.2.2.1 a b, z.2.2.2⟩
    exact ⟨⟨y, hy⟩, e⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h => Subtype.ext (funext fun x => by rw [← hf, ← hf, h])
  have hb' : Nat.card (Z1 ρS) * archH0Card S ρS c ≤ Nat.card M ^ (r + 2 + g + Module.finrank ℚ F) :=
    hb.trans (Nat.pow_le_pow_right hM (by omega))
  refine ⟨CardLe.of_injective ⟨hZ, le_trans (Nat.le_mul_of_pos_right _ ?_) hb'⟩ f hinj, fun hF hcc => ?_⟩
  · unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρS (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  · have ha : archH0Card S ρS c = Nat.card M ^ Module.finrank ℚ F := by
      rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
        Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
      have hw : ∀ w, Nat.card {m : M // ρS (toGS Ω _ (c w)) m = m} = Nat.card M := fun w => by
        obtain ⟨j, hj, -⟩ := hc w (IsTotallyReal.isReal w)
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun m => by rw [h1, hρ', hcc _ ⟨j, hj⟩])
      rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ,
        IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [ha, pow_add _ (r + 2 + g)] at hb'
    exact CardLe.of_injective ⟨hZ, Nat.le_of_mul_le_mul_right hb' (pow_pos hM _)⟩ f hinj
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsIwasawaRankBoundOfFerreroWashington
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cardLe_map_of_cardLe {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (S : Submodule R M) (n : ℕ) (h : CardLe S n) : CardLe (S.map f) n := by
  obtain ⟨hfin, hcard⟩ := h
  have hsurj : Function.Surjective
      (fun x : S => (⟨f x, Submodule.mem_map_of_mem x.2⟩ : S.map f)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans hcard⟩

theorem UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington :
    UpperTheory.V.Published.FerreroWashington → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)), l ≠ 2 → IsOpen (U : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ U → U ≤ (cycMod ℚ Ω l 1).ker → ∃ r : ℕ, ∀ n : ℕ, XRk l 1 (levU l U n) r := by
  intro hFW Ω _ _ _ l _ U hl2 hUo hc hUcyc
  have hl : l.Prime := Fact.out
  have hUc : IsClosed (U : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen U hUo
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U
  have hUK : K.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUc⟩
  haveI : FiniteDimensional ℚ K := (InfiniteGalois.isOpen_iff_finite K).1 (by rw [hUK]; exact hUo)
  haveI : NumberField K := ⟨⟩
  have hgal : galOf ℚ K Ω = U := by
    rw [← hUK]
    ext σ
    simp [UpperTheory.V.Base.galOf, IntermediateField.mem_fixingSubgroup_iff]
  have hnorm : U.Normal := by
    constructor
    intro h hh g
    have hcm : g * h * g⁻¹ * h⁻¹ ∈ U :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact U.mul_mem hcm hh
  haveI : IsGalois ℚ K := (InfiniteGalois.normal_iff_isGalois K).1 (by rw [hUK]; exact hnorm)
  haveI : IsMulCommutative Gal(K/ℚ) := by
    constructor
    constructor
    intro a b
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω a
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω b
    have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) K).ker := by
      erw [IntermediateField.restrictNormalHom_ker K]
      rw [hUK]
      exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ))
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    have h1 := congrArg (· * (AlgEquiv.restrictNormalHom K τ) * (AlgEquiv.restrictNormalHom K σ)) hmem
    simp only [one_mul, inv_mul_cancel_right] at h1
    exact h1
  haveI : IsAbelianGalois ℚ K := ⟨⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hchar : ∀ σ : G ℚ Ω, cycMod ℚ Ω l 1 σ = 1 → galChar Ω (l ^ 1) σ = 1 := by
    intro σ h
    unfold ReciprocityTheory.Gal.cycMod ReciprocityTheory.Gal.cycZ at h
    unfold UpperTheory.V.Two.galChar
    rw [Units.ext_iff] at h ⊢
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h
    erw [cyclotomicCharacter.toZModPow] at h
    exact h
  have hμ : ∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l) := by
    rw [if_neg hl2]
    have := (muIff Ω K (l ^ 1)).2 (by
      rw [hgal]
      intro σ hσ
      exact hchar σ (hUcyc hσ))
    simpa only [pow_one] using this
  obtain ⟨r, hr⟩ := hFW l K hμ
  refine ⟨r, fun n => ?_⟩
  obtain ⟨hcyc, -, -⟩ := UpperTheory.V.Kum.fnCyc K Ω l n
  set K' := UpperTheory.V.Kum.Fn K Ω l n
  haveI : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {l ^ n} K K'
  haveI : FiniteDimensional ℚ K' := Module.Finite.trans K K'
  haveI : NumberField K' := ⟨⟩
  have hcl := hr n K'
  have hgo := UpperTheory.V.Kum.galOfCyc ℚ Ω l n K K'
  rw [hgal] at hgo
  have h2 : ∀ m : ZMod l, 2 • m = 0 → m = 0 := by
    intro m hm
    have h2ne : (2 : ZMod l) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hm
    exact (mul_eq_zero.1 hm).resolve_left h2ne
  have hpull := UpperTheory.V.Kum.pullOnto ℚ Ω K' (levU l U n) hgo.ge 1 (ZMod l) (ZMod l) one_ne_zero hgo.le (Or.inr h2)
  show CardLe (UpperTheory.V.Kum.XDual 1 (levU l U n) (ZMod l) (ZMod l)) (l ^ r)
  rw [← hpull]
  apply cardLe_map_of_cardLe
  have cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
      [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
    refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
    show Nat.card (Module.Dual (ZMod l) V) ≤ _
    rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

  have cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
      (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
      CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
    have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
      intro p c n
      induction n with
      | zero =>
        have h := hm p 1 1
        rw [mul_one] at h
        simpa using h
      | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
    have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
    have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
      intro v
      change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨a, rfl⟩
    let φ : P → A →* Multiplicative (ZMod l) := fun p =>
      { toFun := fun a => Multiplicative.ofAdd (θ p a)
        map_one' := by
          show Multiplicative.ofAdd (θ p 1) = 1
          rw [h1]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (θ p (a * b)) = _
          rw [hm]
          rfl }
    let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
      QuotientGroup.lift _ (φ p) (by
        rintro _ ⟨c, rfl⟩
        show Multiplicative.ofAdd (θ p (c ^ l)) = 1
        rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rfl)
    let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
      AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
        show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
        rw [map_mul]
        rfl)
    have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
    have hinj : Function.Injective Φ := by
      intro p q h
      apply hθ
      funext a
      rw [← hΦ p a, ← hΦ q a, h]
    letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
    exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
      ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
        (M₁ := ZMod l)).comp hinj)
  have hcard : CardLe (UpperTheory.V.Kum.ClDual K' 1 (ZMod l) (ZMod l))
      (Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range)) := by
    exact cardLe_hom (ClassGroup (𝓞 K')) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
  obtain ⟨hf, hle⟩ := hcard
  exact ⟨hf, hle.trans hcl⟩
end

