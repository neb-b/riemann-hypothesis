module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycDescend
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycDescend :
    ∀ (a b : ℕ) [NeZero (a * b)] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {a * b} ℚ C] (ζ : C) (F : IntermediateField ℚ C), a.Coprime b → IsPrimitiveRoot ζ (a * b) → (∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p) → F ≤ ℚ⟮ζ ^ b⟯ := by
  intro a b _ C _ _ _ ζ F hab hζ hunr
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (NeZero.ne (a * b))
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {a * b} ℚ C
  set χ := IsCyclotomicExtension.Rat.galEquivZMod (a * b) C with hχ
  have hcomm : ∀ σ τ : Gal(C/ℚ), τ * σ * τ⁻¹ = σ := by
    intro σ τ
    apply χ.injective
    rw [map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]
  haveI : F.fixingSubgroup.Normal := ⟨fun σ hσ τ => by rw [hcomm]; exact hσ⟩
  have hFF : fixedField F.fixingSubgroup = F := IsGalois.fixedField_fixingSubgroup F
  haveI hgF : IsGalois ℚ F := by
    have h := IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup
    rw [hFF] at h
    convert h
  have hin : ∀ p : ℕ, p.Prime → p ∣ b → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal →
      w.asIdeal.inertia Gal(C/ℚ) ≤ F.fixingSubgroup := by
    intro p hp hpb w hw σ hσ
    have hk := (UpperTheory.V.CF.ineFixQ F C p hp).mp (hunr p hp hpb) w hw hσ
    rw [MonoidHom.mem_ker] at hk
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F C σ ⟨x, hx⟩
    rw [hk, AlgEquiv.one_apply] at hc
    exact hc.symm
  have hsup : ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p ≤
      F.fixingSubgroup.map χ.toMonoidHom := by
    refine iSup₂_le fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 C) (Ideal.span {(p : ℤ)})
    haveI := hPm
    haveI := hPl
    have hpP : (p : 𝓞 C) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
      rw [Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.under_def,
        Ideal.mem_comap] at h1
      simpa using h1
    let w : HeightOneSpectrum (𝓞 C) := ⟨P, hPm.isPrime, fun h => by
      rw [h, Ideal.mem_bot] at hpP
      exact (Nat.cast_ne_zero.mpr hpp.ne_zero) hpP⟩
    rw [← KStar.Ram.map_inertia_eq p P]
    exact Subgroup.map_mono (hin p hpp hpb w hpP)
  rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ ^ b⟯, IntermediateField.le_iff_le]
  intro σ hσ
  have hfix : σ (ζ ^ b) = ζ ^ b := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hker : χ σ ∈ (ZMod.unitsMap (Dvd.intro b rfl : a ∣ a * b)).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
    rw [map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (a * b) C σ hζ.pow_eq_one,
      ← pow_mul] at hfix
    have hmod : (χ σ).val.val * b ≡ 1 * b [MOD a * b] := by
      rw [one_mul]
      have h2 := (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp hfix
      rw [← hζ.eq_orderOf] at h2
      exact h2
    have hk := Nat.ModEq.mul_right_cancel' hb0 hmod
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk
  have hmem := hsup (UpperTheory.V.CF.unitsGen a b hab hker)
  rw [Subgroup.mem_map] at hmem
  obtain ⟨τ, hτ, hτσ⟩ := hmem
  have hτσ' : τ = σ := χ.injective hτσ
  rwa [hτσ'] at hτ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsPrimeMemOfMem
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem exists_prime_mem_of_mem {R : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ I → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one I).mpr (by simpa using hmem)) hI.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      rw [hm, Nat.cast_mul] at hmem
      rcases hI.mem_or_mem hmem with h | h
      · exact ⟨_, hp, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          conv_rhs => rw [hm]
          exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
        exact ih m hlt hm0 h

private theorem cyc_adjoin (K : Type) {L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} K K⟮ζ⟯ := by
  change IsCyclotomicExtension {n} K (IntermediateField.adjoin K {ζ}).toSubalgebra
  have hi : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

theorem UpperTheory.V.CF.kwRay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (𝔪 : GroundTheory.Global.Modulus ℚ) (ζ : Ω), IsPrimitiveRoot ζ (Ideal.absNorm 𝔪.ideal) → 𝔪.rayClassField Ω ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ 𝔪 ζ hζ
  set N := Ideal.absNorm 𝔪.ideal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔪.ideal_ne_bot
  haveI : NeZero N := ⟨hN0⟩
  have hcyc := cyc_adjoin ℚ hζ
  haveI : NumberField ℚ⟮ζ⟯ := @IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯ _ _ _ _ _ hcyc
  have hgal := @IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯ _ _ _ hcyc
  haveI := (GroundTheory.Global.Modulus.isAbelianGalois_rayClassField 𝔪 Ω).toIsGalois
  have hfin : ({v | v.asIdeal ∣ 𝔪.ideal} ∪ {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}} :
      Set (HeightOneSpectrum (𝓞 ℚ))).Finite := by
    refine (Ideal.finite_factors 𝔪.ideal_ne_bot).union (Ideal.finite_factors ?_)
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  refine @UpperTheory.V.CF.bauer ℚ Ω _ _ _ _ (𝔪.rayClassField Ω) ℚ⟮ζ⟯ _ _ _
    (by convert hgal) _ hfin ?_
  intro v hv hsplit
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨_, hv2⟩ := hv
  rw [Ideal.dvd_span_singleton] at hv2
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_of_mem v.asIdeal v.isPrime
    (Ideal.absNorm v.asIdeal) (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    (Ideal.absNorm_mem _)
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, hk⟩
    apply hv2
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hmod : p ≡ 1 [MOD N] := by
    haveI hc2 : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
      convert hcyc
      all_goals first
        | rfl
        | exact Subsingleton.elim _ _
    refine UpperTheory.V.CF.splitCyc N ℚ⟮ζ⟯ v p hp hpv hpN ?_
    convert hsplit
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
  obtain ⟨hv', hcls⟩ := UpperTheory.V.CF.rayPrime 𝔪 v p hp hpv hmod
  exact (GroundTheory.Global.Modulus.splitsCompletely_rayClassField_iff 𝔪 Ω hv').mpr hcls
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkGen
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.minkGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], (⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ)) = ⊤ := by
  intro K _ _ _
  set I : Subgroup Gal(K/ℚ) := ⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ) with hI
  have hconj : ∀ (τ : Gal(K/ℚ)) (w : HeightOneSpectrum (𝓞 K)), ∃ w' : HeightOneSpectrum (𝓞 K),
      ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), τ * σ * τ⁻¹ ∈ w'.asIdeal.inertia Gal(K/ℚ) := by
    intro τ w
    refine ⟨⟨τ • w.asIdeal, by haveI := w.isPrime; infer_instance, ?_⟩, ?_⟩
    · intro h
      apply w.ne_bot
      rw [eq_bot_iff]
      intro x hx
      have hx' : τ • x ∈ τ • w.asIdeal := Ideal.smul_mem_pointwise_smul τ x _ hx
      rw [h, Ideal.mem_bot] at hx'
      rw [Ideal.mem_bot]
      exact (smul_eq_zero_iff_eq τ).mp hx'
    · intro σ hσ x
      have hm := Ideal.smul_mem_pointwise_smul τ _ w.asIdeal (hσ (τ⁻¹ • x))
      rwa [smul_sub, smul_inv_smul, ← mul_smul, ← mul_smul] at hm
  haveI hN : I.Normal := by
    constructor
    intro σ hσ τ
    have hle : I ≤ I.comap (MulAut.conj τ).toMonoidHom := by
      refine iSup_le fun w => ?_
      obtain ⟨w', hw'⟩ := hconj τ w
      intro σ' hσ'
      exact le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w' (hw' σ' hσ')
    exact hle hσ
  set F := IntermediateField.fixedField I with hF
  haveI hFgal := IsGalois.of_fixedField_normal_subgroup I
  haveI hgF : IsGalois ℚ F := by
    convert hFgal
  have hunr : ∀ p, Nat.Prime p → UnramAt F p := by
    intro p hp
    refine (UpperTheory.V.CF.ineFixQ F K p hp).mpr ?_
    intro w _ σ hσ
    rw [MonoidHom.mem_ker]
    ext x
    rw [AlgEquiv.one_apply]
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F K σ x
    exact hc.trans ((IntermediateField.mem_fixedField_iff I _).mp x.2 σ
      (le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w hσ))
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra h
    obtain ⟨p, hp, hnot⟩ := UpperTheory.V.CF.minkRam F h
    exact hnot (hunr p hp)
  have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField I, ← hF, hbot,
    IntermediateField.fixingSubgroup_bot]
end

