module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0013
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FiniteCompactlySupportedH1
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem ker_open {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (h : ContAction ρ) :
    IsOpen (ρ.ker : Set Γ) := by
  let b := Module.finBasis k M
  have hset : (ρ.ker : Set Γ) = ⋂ i, {g | ρ g (b i) = b i} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg i
      rw [hg]
      rfl
    · intro hg
      exact b.ext fun i => by simpa using hg i
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous fun g : Γ => ρ g (b i) :=
    (show Continuous fun p : Γ × M => ρ p.1 p.2 from h).comp (continuous_id.prodMk continuous_const)
  exact hc.isOpen_preimage {b i} (isOpen_discrete _)

private theorem finite_compactly_supported_H1 {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)
    [Module.Finite k (H1 ρ)] : Module.Finite k (F.H1c ρ) := by
  have hB : (B1 ρ).FG := by
    show (LinearMap.range (d0 ρ)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian k ↥(B1 ρ) := isNoetherian_of_fg_of_noetherian _ hB
  have hK : (Submodule.comap (Z1 ρ).subtype (B1 ρ)).FG :=
    Submodule.fg_of_fg_map_injective (Z1 ρ).subtype Subtype.val_injective
      (Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _))
  have hZ : (⊤ : Submodule k ↥(Z1 ρ)).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Submodule.comap (Z1 ρ).subtype (B1 ρ)))
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, Submodule.ker_mkQ]
      exact hK
  haveI : Module.Finite k ↥(Z1 ρ) := ⟨hZ⟩
  have hZ1 : (Z1 ρ).FG := Module.Finite.iff_fg.mp inferInstance
  have hP : ((Z1 ρ).prod (⊤ : Submodule k (F.T → M))).FG := hZ1.prod Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : F.H1c ρ ≤ (Z1 ρ).prod ⊤ := by
    rintro x ⟨hlc, hcoc, -, -, -⟩
    exact ⟨⟨hlc.continuous, hcoc⟩, trivial⟩
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

theorem UpperTheory.V.X.framed_h1_euler_formula :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (F.H1c ρ) ∧ finrank k (F.H1c ρ) + finrank k (H0 ρ) = finrank k (selF F ρ) + ∑ v, finrank k (H0 (ρ.comp (F.φ v))) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ hc hN hH
  refine ⟨finite_compactly_supported_H1 F ρ, ?_⟩
  have e := Alg.finrank_compact_support_H1 k Γ M ρ (ker_open ρ hc) F hN hH
  have hs : finrank k ↥(selF F ρ) = finrank k ↥(Sha1 ρ F.φ F.hφ ⊓
      Sel ρ F.ψ F.hψ fun q => H1ur (ρ.comp (F.ψ q)) (F.N q)) := rfl
  rw [hs]
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem hom_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k) (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) k (PadicInt.toZModPow 1 x) = f x := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (PadicInt.toZModPow 1 x)
  have h : x - n ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, map_intCast, hn, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  rw [← hn, map_intCast, sub_eq_iff_eq_add.1 hy, map_add (f := _), map_mul, map_pow, map_natCast, CharP.cast_eq_zero, map_intCast]
  simp

theorem UpperTheory.V.X.cycKFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], (∀ σ : G ℚ Ω, IsCC σ → cycK Ω l k σ = -1) ∧ ∀ (c : Coef l) (red : c.O →+* k) (g : G ℚ Ω), (cycK Ω l k g : k) = red (chiO ℚ Ω l c.O g : c.O) := by
  intro Ω _ _ _ l hl k _ _
  refine ⟨fun σ hσ => ?_, fun c red g => hom_eq (red.comp (algebraMap ℤ_[l] c.O)) (cycZ ℚ Ω l g : ℤ_[l]ˣ)⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  have h1 : Chr.cls ℚ Ω (l ^ 1) σ = cycMod ℚ Ω l 1 σ := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω σ) ζ hζ
  have h2 : Chr.cls ℚ Ω (l ^ 1) σ = -1 := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
  refine Units.ext ?_
  show ZMod.castHom (dvd_pow_self l one_ne_zero) k (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) = _
  rw [← h1, h2]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDecZhat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology UpperTheory.V.Base

private theorem dz_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst ψ h

private theorem dz_exists_prime (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 ℚ) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk11.dz_exists_prime v n hn h

private theorem dz_not_both (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 ℚ) ∈ v.asIdeal)
    (hb : (b : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 ℚ) (b : 𝓞 ℚ) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem dz_val {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 ℚ)
  have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem dz_order {q n m : ℕ} (hq : 1 < q) (hn : 0 < n) (hm : m + 1 = q ^ n) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q) : orderOf u = n := by
  rw [orderOf_eq_iff hn]
  refine ⟨Units.ext ?_, fun k hk hk0 h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu, ← Nat.cast_pow, ← hm]
    simp
  · have h1 : ((q ^ k : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
      rw [Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h]
      simp
    have h2 : 1 < q ^ k := Nat.one_lt_pow hk0.ne' hq
    have h3 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h4 := (Nat.modEq_iff_dvd' h2.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
    have h5 := Nat.le_of_dvd (by omega) h4
    omega

private theorem dz_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : IsPlaceOver A v) (D I : Subgroup (G ℚ Ω)) (hD : D = Dec (F := ℚ) A) (hI : I = Ine (F := ℚ) A) :
    ∃ φ : D, (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω)
      ⟨(Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := ℚ) A ≤ (Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := ℚ) A)).map (Dec (F := ℚ) A).subtype =
        Ine (F := ℚ) A ⊔ Subgroup.zpowers γ := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_eq_left.2 (Ine_le_Dec A)]
      rfl
    rw [eq_top_iff]
    intro x _
    have h3 := h1 x.2
    rw [← h2] at h3
    exact closure_subtype.2 h3
  · have hq : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq1 : 1 < normV v := by
      rw [hq]
      have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      omega
    have hqv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
    obtain ⟨p, hp, hpq, hpv⟩ := dz_exists_prime v _ (by omega) hqv
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : 1 < normV v ^ n := Nat.one_lt_pow hn.ne' hq1
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = normV v ^ n := ⟨normV v ^ n - 1, by omega⟩
    haveI : NeZero m := ⟨by omega⟩
    have hmp : m.Coprime p := by
      refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_).symm
      have h2 : p ∣ m + 1 := hm ▸ hpq.trans (dvd_pow_self _ hn.ne')
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
    have hA := (dz_val hv p).2 hpv
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω m
    have hI := hIne A fun h => dz_not_both v hmp ((dz_val hv m).1 h) hpv
    have hu : ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots ℚ Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := dz_order hq1 hn hm _ hu
    have hle : Dec (F := ℚ) A ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) := by
      have hk : (Chr.cls ℚ Ω m).ker ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen ℚ Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := ℚ) A →* Subgroup.zpowers (Chr.cls ℚ Ω m γ) :=
      ((Chr.cls ℚ Ω m).comp (Dec (F := ℚ) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls ℚ Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls ℚ Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := ℚ) A, Chr.cls ℚ Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, dz_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.decZhat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ φ : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : Dec (F := ℚ) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro Ω _ _ _ p hp A hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := hP.1 fun h => (hP.2.1 h).2 hA
  exact dz_frob Ω A v hv _ _ rfl rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.dirVal :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (g : G ℚ Ω), ∃ a : ℤ, IsCoprime a M ∧ ∀ (N : ℕ) [NeZero N], N ∣ M → ∀ (O : Type) [CommRing O] (χ : DirichletCharacter O N), (Chr.dirG ℚ Ω χ g : O) = χ a := by
  intro Ω _ _ _ M _ g
  refine ⟨(((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ), ?_, fun N _ h O _ χ => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime _)
  · have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω M).2.1 N h) g
    have h2 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = ((((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) := by
      rw [← h1, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
    rw [Int.cast_natCast, ← h2]
    exact MulChar.coe_toUnitHom χ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.GaloisIndexPlaces

private theorem prime_p {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact h

private noncomputable def vQ (l : ℕ) (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_p hl).ne_zero).mpr (prime_p hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_p hl).ne_zero

private theorem mem_vQ (l : ℕ) (hl : l.Prime) : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l hl).asIdeal :=
  Ideal.mem_span_singleton_self _

private theorem eq_vQ (l : ℕ) (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    vQ l hl = v := by
  apply HeightOneSpectrum.ext
  have hle : (vQ l hl).asIdeal ≤ v.asIdeal := by
    show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h
  exact (vQ l hl).isMaximal.eq_of_le v.isPrime.ne_top hle

private theorem vQ_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : vQ p hp = vQ q hq) : p = q := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (vQ q hq).asIdeal := h ▸ mem_vQ p hp
  have h2 : ((q : ℕ) : 𝓞 ℚ) ∣ ((p : ℕ) : 𝓞 ℚ) := Ideal.mem_span_singleton.1 h1
  have h3 := map_dvd Rat.ringOfIntegersEquiv h2
  simp only [map_natCast] at h3
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h3)).symm

private theorem isPlaceOver_vQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hl : l.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l hl) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hne, htop, hab, -⟩ := UpperTheory.V.Base.places ℚ Ω l A
  have hAT : A ≠ ⊤ := by
    intro hT
    exact (htop hT).2 hA
  obtain ⟨v, hv⟩ := hne hAT
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (hab v hv).mp hA
  rw [eq_vQ l hl v hlv]
  exact hv

end UpperTheory.V.X.GaloisIndexPlaces

open UpperTheory.V.X.GaloisIndexPlaces in
theorem UpperTheory.V.X.galIdx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (e : T ⊕ Q ≃ S), SP = S ∧ (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) ∧ (∀ v : T, IsPlaceOver (pl v) (e (.inl v)).1) ∧ ∀ q : Q, IsPlaceOver (pl q) (e (.inr q)).1 := by
  classical
  intro Ω _ _ _ l SP T Q v0 pl K hD
  have hex : ∃ f : ℕ → HeightOneSpectrum (𝓞 ℚ), ∀ (p : ℕ) (hp : Nat.Prime p), f p = vQ p hp :=
    ⟨fun p => if hp : Nat.Prime p then vQ p hp else vQ 2 Nat.prime_two, fun p hp => dif_pos hp⟩
  obtain ⟨f, hf⟩ := hex
  have hpr : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime := hD.prime
  have hmemS : ∀ p, p ∈ T ∨ p ∈ Q → f p ∈ (T ∪ Q).image f := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_union.mpr hp)
  have hfinj : ∀ p q, (p ∈ T ∨ p ∈ Q) → (q ∈ T ∨ q ∈ Q) → f p = f q → p = q := by
    intro p q hp hq he
    rw [hf p (hpr p hp), hf q (hpr q hq)] at he
    exact vQ_inj _ _ he
  let g : T ⊕ Q → (T ∪ Q).image f := fun x => match x with
    | .inl p => ⟨f p, hmemS p (Or.inl p.2)⟩
    | .inr q => ⟨f q, hmemS q (Or.inr q.2)⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) he <;> simp only [g, Subtype.mk.injEq] at he
      · have := hfinj a b (Or.inl ha) (Or.inl hb) he
        subst this
        rfl
      · have := hfinj a b (Or.inl ha) (Or.inr hb) he
        subst this
        exact absurd hb (Finset.disjoint_left.mp hD.disj ha)
      · have := hfinj a b (Or.inr ha) (Or.inl hb) he
        subst this
        exact absurd ha (Finset.disjoint_left.mp hD.disj hb)
      · have := hfinj a b (Or.inr ha) (Or.inr hb) he
        subst this
        rfl
    · rintro ⟨s, hs⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨.inl ⟨p, hp⟩, rfl⟩
      · exact ⟨.inr ⟨p, hp⟩, rfl⟩
  refine ⟨(T ∪ Q).image f, Equiv.ofBijective g hg, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [hD.mem v, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hpv⟩
      refine ⟨p, Finset.mem_union.mpr hp, ?_⟩
      rw [hf p (hpr p hp)]
      exact eq_vQ p _ v hpv
    · rintro ⟨p, hp, rfl⟩
      have hp' := Finset.mem_union.mp hp
      refine ⟨p, hp', ?_⟩
      rw [hf p (hpr p hp')]
      exact mem_vQ p _
  · intro v hv
    have hl : l ∈ T ∨ l ∈ Q := Or.inl hD.l_mem
    have : f l = v := by
      rw [hf l (hpr l hl)]
      exact eq_vQ l _ v hv
    rw [← this]
    exact hmemS l hl
  · intro p
    have hp : (p : ℕ) ∈ T ∨ (p : ℕ) ∈ Q := Or.inl p.2
    show IsPlaceOver (pl p) (f p)
    rw [hf p (hpr p hp)]
    exact isPlaceOver_vQ p _ (pl p) (hD.isOver p hp)
  · intro q
    have hq : (q : ℕ) ∈ T ∨ (q : ℕ) ∈ Q := Or.inr q.2
    show IsPlaceOver (pl q) (f q)
    rw [hf q (hpr q hq)]
    exact isPlaceOver_vQ q _ (pl q) (hD.isOver q hq)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGlobEuler
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ inst _ l _ hl S hS k _ _ _ M _ _ _ _ _ ρ hρ σ hσ
  have hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hM : Finite M := Module.finite_of_finite k
  exact UpperTheory.global_euler_characteristic_rationals_odd_prime hF hE Ω l hl k M S ρ hS hρ σ hσ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPrimProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.primProd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter O M) (θ : DirichletCharacter O N), ∃ (f : ℕ) (φ : DirichletCharacter O f), φ.IsPrimitive ∧ f ∣ M * θ.conductor ∧ (∀ t : ℕ, χ ^ t = 1 → θ ^ t = 1 → φ ^ t = 1) ∧ ∀ a : ℤ, IsCoprime a (M * N : ℕ) → φ a = χ a * θ a := by
  intro O _ _ M N _ _ χ θ
  have hc0 : θ.conductor ≠ 0 := θ.conductor_ne_zero
  haveI : NeZero θ.conductor := ⟨hc0⟩
  haveI : NeZero (M * θ.conductor) := ⟨mul_ne_zero (NeZero.ne M) hc0⟩
  set θ' := θ.primitiveCharacter with hθe
  have hM : M ∣ M * θ.conductor := dvd_mul_right M _
  have hC : θ.conductor ∣ M * θ.conductor := dvd_mul_left _ M
  set ψ : DirichletCharacter O (M * θ.conductor) :=
    DirichletCharacter.changeLevel hM χ * DirichletCharacter.changeLevel hC θ' with hψe
  refine ⟨ψ.conductor, ψ.primitiveCharacter, ψ.primitiveCharacter_isPrimitive, ψ.conductor_dvd_level, ?_, ?_⟩
  · intro t hχ hθ
    have hθ1 : θ' ^ t = 1 := by
      rw [← DirichletCharacter.changeLevel_eq_one_iff θ.conductor_dvd_level, map_pow,
        DirichletCharacter.changeLevel_primitiveCharacter]
      exact hθ
    have hψ1 : ψ ^ t = 1 := by
      rw [hψe, mul_pow, ← map_pow, ← map_pow, hχ, hθ1, map_one, map_one, mul_one]
    rw [← DirichletCharacter.changeLevel_eq_one_iff ψ.conductor_dvd_level, map_pow,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact hψ1
  · intro a ha
    rw [Nat.cast_mul] at ha
    have haM : IsCoprime a (M : ℤ) := ha.of_mul_right_left
    have haN : IsCoprime a (N : ℤ) := ha.of_mul_right_right
    have haC : IsCoprime a (θ.conductor : ℤ) :=
      haN.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr θ.conductor_dvd_level)
    have haMC : IsCoprime a ((M * θ.conductor : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      exact haM.mul_right haC
    rw [ψ.primitiveCharacter_apply_of_isCoprime haMC, hψe, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hM haMC,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' θ' hC haMC,
      θ.primitiveCharacter_apply_of_isCoprime haN]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcScalDim
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.scalDim :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k Γ M) (γ χ : Γ →* kˣ), (∀ g m, ρ g m = (γ g : k) • m) → (∀ σ, γ σ = 1 → finrank k (LinearMap.ker (ρ σ - 1)) = finrank k M) ∧ (∀ σ, (finrank k M = 0 ∨ γ σ ≠ 1) → finrank k (LinearMap.ker (ρ σ - 1)) = 0) ∧ ((finrank k M = 0 ∨ ∃ g, γ g ≠ χ g) → finrank k (Loc.H0dual χ ρ) = 0) := by
  intro k Γ M _ _ _ _ _ ρ γ χ h
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun hσ => ?_⟩
  · have : LinearMap.ker (ρ σ - 1) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      simp [h, hσ]
    rw [this, finrank_top]
  · have : LinearMap.ker (ρ σ - 1) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      rw [Submodule.mem_bot]
      rcases hσ with h0 | h0
      · exact (finrank_zero_iff_forall_zero.mp h0) m
      · have h1 : ((γ σ : k) - 1) • m = 0 := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, h] at hm
          rw [sub_smul, one_smul]
          exact hm
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact absurd (Units.ext (sub_eq_zero.mp h2)) h0
        · exact h2
    rw [this, finrank_bot]
  · have : Loc.H0dual χ ρ = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_bot]
      ext m
      rcases hσ with h0 | ⟨g, hg⟩
      · rw [(finrank_zero_iff_forall_zero.mp h0) m]; simp
      · have h1 := hf g m
        rw [h, map_smul, smul_eq_mul] at h1
        have h2 : ((γ g : k) - χ g) * f m = 0 := by
          rw [sub_mul, h1]; simp
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Units.ext (sub_eq_zero.mp h3)) hg
        · simpa using h3
    rw [this, finrank_bot]
end

