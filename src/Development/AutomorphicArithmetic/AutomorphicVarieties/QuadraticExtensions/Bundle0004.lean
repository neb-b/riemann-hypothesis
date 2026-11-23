module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abField :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (L : Type) [Field L] [NumberField L] [Algebra L Ω], IsAbField A L → galOf ℚ L Ω = abU Ω A := by
  intro Ω _ _ _ A L _ _ _ hL
  obtain ⟨N, hN, j, ζ, hm, hζ, hj⟩ := hL
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ (CyclotomicField N ℚ) := by
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
    have h := CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)
    have h2 := (@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal
    convert h2
    exact Subsingleton.elim _ _
  let k : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H := by
    intro σ
    let τ := σ.restrictNormal (CyclotomicField N ℚ)
    have hτ : ∀ y, k (τ y) = σ (k y) := fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y
    have hkζ : IsPrimitiveRoot (k ζ) N := hζ.map_of_injective k.injective
    have hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val :=
      galChar_spec N σ (k ζ) hkζ.pow_eq_one
    have hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val := by
      apply k.injective
      show k (τ ζ) = k (ζ ^ _)
      rw [hτ, hσζ, map_pow]
    have h1 := hj τ _ hτζ
    have hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x)) :=
      forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm
    rw [← hfix, h1]
    obtain ⟨d, hd⟩ := hm
    have hprim : IsPrimitiveRoot (k ζ ^ d) A.m :=
      hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))
    have e1 := galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one
    rw [map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul] at e1
    have hfin : IsOfFinOrder (k ζ ^ d) := isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩
    have hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m] := by
      have h2 := hfin.pow_eq_pow_iff_modEq.1 e1
      rwa [← hprim.eq_orderOf] at h2
    have hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]
    constructor
    · rintro ⟨u, hu, hua⟩
      have hu' : u = galChar Ω A.m σ := Units.ext (hua.trans hcast)
      exact hu' ▸ hu
    · intro h
      exact ⟨_, h, hcast.symm⟩
  let σ₀ : Ω →ₐ[ℚ] Ω := j.liftNormal Ω
  have hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x) := fun x => j.liftNormal_commutes Ω x
  let e : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have he : ∀ x : L, e (algebraMap L Ω x) = k (j x) := hσ₀
  have hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ := by
    intro σ
    rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]
  ext σ
  change (∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H
  rw [← hconj σ, ← key]
  refine forall_congr' fun x => ?_
  rw [← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    e.injective.eq_iff]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CompIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem exists_isPrimitiveRoot_of_isAlgClosure_rat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n] :
    ∃ ω : Ω, IsPrimitiveRoot ω n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

private theorem coe_galChar_eq_natCast_of_apply_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) (c : ℕ) (hc : σ ω = ω ^ c) :
    ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n) = (c : ZMod n) := by
  have hc' : σ ω = ω ^ (c % n) := by
    rw [hc]
    conv_lhs => rw [← Nat.mod_add_div c n, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have htn : (t : Ω) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one htn
  rw [← hi, ZMod.val_natCast]
  change σ (ω ^ i) = _
  rw [map_pow, hc', ← pow_mul, ← pow_mul, mul_comm]

private theorem apply_eq_pow_val_galChar_of_isPrimitiveRoot (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) :
    σ ω = ω ^ ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n).val := by
  have := modularCyclotomicCharacter.spec Ω (n := n) (by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n) σ.toRingEquiv (t := (hω.toRootsOfUnity : Ωˣ)) (SetLike.coe_mem _)
  simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] at this
  exact this

private theorem coe_galChar_eq_val_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω m σ : (ZMod m)ˣ) : ZMod m).val : ZMod k) := by
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_of_isAlgClosure_rat Ω m
  obtain ⟨r, hr⟩ := hkm
  have hω' : IsPrimitiveRoot (ω ^ r) k := hω.pow (Nat.pos_of_neZero m) (by rw [hr, mul_comm])
  apply coe_galChar_eq_natCast_of_apply_eq_pow Ω k σ _ hω'
  rw [map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω m σ ω hω, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ZMod.unitsMap hkm (galChar Ω m σ) = galChar Ω k σ := by
  ext
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, coe_galChar_eq_val_galChar_of_dvd Ω k m hkm σ]

private theorem mem_comap_cycZ_princ_two_iff_galChar_eq_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (σ : G ℚ Ω) :
    σ ∈ Subgroup.comap (cycZ ℚ Ω 2) (KStar.TotallyRealRoots.princ 2 n) ↔ galChar Ω (2 ^ n) σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (2 ^ i) := fun i => inferInstance
  rw [Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, Units.ext_iff, Units.ext_iff]
  change PadicInt.toZModPow n ((cyclotomicCharacter Ω 2 σ.toRingEquiv : ℤ_[2]ˣ) : ℤ_[2]) = 1 ↔ _
  rw [cyclotomicCharacter.toZModPow]
  rfl

private theorem mem_galOf_iff_val_galChar_of_fixes_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (E : Type) [Field E]
    [NumberField E] [Algebra E Ω] (N : ℕ) [NeZero N] (j : E →ₐ[ℚ] CyclotomicField N ℚ)
    (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N) (Q : ℕ → Prop)
    (hQ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a : ℕ), τ ζ = ζ ^ a → ((∀ x, τ (j x) = j x) ↔ Q a))
    (σ : G ℚ Ω) : σ ∈ galOf ℚ E Ω ↔ Q ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hce0 := CyclotomicField.isCyclotomicExtension N ℚ
  have hce : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := by exact hce0
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := by
    exact IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let ι : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast, eq_ratCast, map_ratCast])
  let φ := (ι.comp j).liftNormal Ω
  let ρ : G ℚ Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  have hρ : ∀ x : E, ρ (algebraMap E Ω x) = ι (j x) := fun x => (ι.comp j).liftNormal_commutes Ω x
  let σ' : G ℚ Ω := ρ * σ * ρ⁻¹
  have hgal : galChar Ω N σ' = galChar Ω N σ := by
    simp only [σ', map_mul, map_inv]
    rw [mul_comm (galChar Ω N ρ), mul_assoc, mul_inv_cancel, mul_one]
  let τ : Gal(CyclotomicField N ℚ/ℚ) := σ'.restrictNormal (CyclotomicField N ℚ)
  have hτ : ∀ y, ι (τ y) = σ' (ι y) := fun y => AlgEquiv.restrictNormal_commutes σ' (CyclotomicField N ℚ) y
  have hτζ : τ ζ = ζ ^ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    apply ι.toRingHom.injective
    change ι (τ ζ) = ι (ζ ^ _)
    rw [hτ, map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω N σ' (ι ζ) (hζ.map_of_injective ι.toRingHom.injective), hgal]
  rw [← hQ τ _ hτζ, mem_galOf]
  apply forall_congr'
  intro x
  rw [← ι.toRingHom.injective.eq_iff]
  change _ ↔ ι (τ (j x)) = ι (j x)
  rw [hτ, ← hρ x]
  simp only [σ', AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  exact ρ.injective.eq_iff.symm

private theorem zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime (p m : ℕ) (hp : p.Prime) (hm : m = p) (a : ℕ) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = a) :
    u ∈ (powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).range ↔ jacobiSym (a : ℤ) p = 1 := by
  subst hm
  haveI : Fact m.Prime := ⟨hp⟩
  have ha0 : (((a : ℤ)) : ZMod m) ≠ 0 := by
    rw [Int.cast_natCast, ← hu]
    exact u.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff m ha0, Int.cast_natCast, ← hu,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [pow_two]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [pow_two, hr]

private theorem mem_abU_sup_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A B : AbF) (σ : G ℚ Ω) :
    σ ∈ abU Ω (A.sup B) ↔ σ ∈ abU Ω A ∧ σ ∈ abU Ω B := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero B.m := ⟨B.pos.ne'⟩
  haveI : NeZero (A.sup B).m := ⟨(A.sup B).pos.ne'⟩
  have h1 : A.m ∣ (A.sup B).m := Dvd.intro B.m rfl
  have h2 : B.m ∣ (A.sup B).m := Dvd.intro_left A.m rfl
  have e1 := unitsMap_galChar_of_dvd Ω A.m (A.sup B).m h1 σ
  have e2 := unitsMap_galChar_of_dvd Ω B.m (A.sup B).m h2 σ
  change (ZMod.unitsMap h1 (galChar Ω (A.sup B).m σ) ∈ A.H ∧
    ZMod.unitsMap h2 (galChar Ω (A.sup B).m σ) ∈ B.H) ↔
    (galChar Ω A.m σ ∈ A.H ∧ galChar Ω B.m σ ∈ B.H)
  rw [e1, e2]

theorem UpperTheory.V.Two.compIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] [Algebra E Ω], q.Prime → d.Prime → IsCompField M e q d E →
      levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω ∧ (levU 2 (abU Ω (base2 M q d)) (e + 2)).relIndex (galOf ℚ E Ω) ∣ 2 := by
  intro Ω _ _ _ M e q d E _ _ _ hq hd hE
  obtain ⟨N, hN, j, ζ, h2N, hMN, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hN
  haveI : NeZero M.m := ⟨M.pos.ne'⟩
  haveI : NeZero (AbF.cyc 4).m := ⟨(AbF.cyc 4).pos.ne'⟩
  haveI : NeZero (AbF.quad q).m := ⟨(AbF.quad q).pos.ne'⟩
  haveI : NeZero (AbF.quad d).m := ⟨(AbF.quad d).pos.ne'⟩
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hqm : (AbF.quad q).m = q := max_eq_left hq.one_lt.le
  have hdm : (AbF.quad d).m = d := max_eq_left hd.one_lt.le
  have h4m : (AbF.cyc 4).m = 4 := rfl
  have key := fun σ => mem_galOf_iff_val_galChar_of_fixes_iff Ω E N j ζ hζ _ hτ σ
  have hlev : ∀ σ : G ℚ Ω, σ ∈ levU 2 (abU Ω (base2 M q d)) (e + 2) ↔
      ((galChar Ω M.m σ ∈ M.H ∧ galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H) ∧
        galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ∧ galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H) ∧
        galChar Ω (2 ^ (e + 2)) σ = 1 := by
    intro σ
    rw [← mem_comap_cycZ_princ_two_iff_galChar_eq_one Ω (e + 2) σ]
    change σ ∈ abU Ω (base2 M q d) ∧ _ ↔ _
    simp only [base2, withI, mem_abU_sup_iff, and_assoc]
    rfl
  have hval : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ZMod k) :=
    fun k _ hk σ => coe_galChar_eq_val_galChar_of_dvd Ω k N hk σ
  have hone : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      (galChar Ω k σ = 1 ↔ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD k]) := by
    intro k _ hk σ
    rw [Units.ext_iff, hval k hk σ, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  have hker : ∀ σ : G ℚ Ω, galChar Ω M.m σ ∈ M.H ↔ M.ker ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    intro σ
    constructor
    · intro h
      exact ⟨_, h, hval M.m hMN σ⟩
    · rintro ⟨u, hu, hua⟩
      have : u = galChar Ω M.m σ := Units.ext (by rw [hua, hval M.m hMN σ])
      rwa [← this]
  have hsq : ∀ σ : G ℚ Ω, (galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) q = 1) ∧
      (galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) d = 1) := by
    intro σ
    exact ⟨zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime q _ hq hqm _ _ (hval _ (by rw [hqm]; exact hqN) σ),
      zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime d _ hd hdm _ _ (hval _ (by rw [hdm]; exact hdN) σ)⟩
  have h4 : ∀ σ : G ℚ Ω, galChar Ω (2 ^ (e + 2)) σ = 1 → galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H := by
    intro σ h
    have h4N : (AbF.cyc 4).m ∣ N := by
      rw [h4m]
      exact dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h2N
    rw [hone _ h2N] at h
    have h1 : galChar Ω (AbF.cyc 4).m σ = 1 := by
      rw [hone _ h4N, h4m]
      exact Nat.ModEq.of_dvd (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h
    rw [h1]
    exact Subgroup.one_mem _
  have hle : levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω := by
    intro σ hσ
    rw [hlev] at hσ
    obtain ⟨⟨⟨hM, -⟩, hQ, hD⟩, h2⟩ := hσ
    rw [key]
    exact ⟨Or.inl ((hone _ h2N σ).1 h2), (hker σ).1 hM, (hsq σ).1.1 hQ, (hsq σ).2.1 hD⟩
  refine ⟨hle, ?_⟩
  have hsub : (galChar Ω (2 ^ (e + 2))).ker.subgroupOf (galOf ℚ E Ω) ≤
      (levU 2 (abU Ω (base2 M q d)) (e + 2)).subgroupOf (galOf ℚ E Ω) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf, hlev]
    obtain ⟨-, hM, hQ, hD⟩ := (key x).1 x.2
    exact ⟨⟨⟨(hker _).2 hM, h4 _ hx⟩, (hsq _).1.2 hQ, (hsq _).2.2 hD⟩, hx⟩
  refine dvd_trans (Subgroup.index_dvd_of_le hsub) ?_
  rw [Subgroup.subgroupOf, MonoidHom.comap_ker, Subgroup.index_ker]
  have hrange : ((galChar Ω (2 ^ (e + 2))).comp (galOf ℚ E Ω).subtype).range ≤ Subgroup.zpowers (-1) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨h12, -⟩ := (key x).1 x.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rcases h12 with h1 | h1
    · rw [(hone _ h2N x).2 h1]
      exact Subgroup.one_mem _
    · have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
      have hm1 : galChar Ω (2 ^ (e + 2)) x = -1 := by
        ext
        rw [Units.val_neg, Units.val_one, hval _ h2N x, eq_neg_iff_add_eq_zero]
        push_cast at hc
        exact hc
      rw [hm1]
      exact Subgroup.mem_zpowers _
  refine dvd_trans (Subgroup.card_dvd_of_le hrange) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DecIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.decIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p c : ℕ) (A₀ : ValuationSubring Ω), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → A₀.valuation (p : Ω) < 1 →
      ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≠ 0 ∧ ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≤ c := by
  intro Ω _ _ _ p c A₀ hp hc hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgζ⟩ := decFrob Ω p A₀ hA
  have hodd : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left, Nat.odd_iff]; omega
  have hu : ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = p := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ n)
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val :=
      cyclotomicCharacter.spec 2 (n := n) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
    have h2 := hgζ (2 ^ n) (Nat.Coprime.pow_left n hodd) ζ hζ.pow_eq_one
    rw [h2] at h1
    have h3 : p ≡ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val [MOD 2 ^ n] := by
      have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by positivity)
      rwa [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val]
  have hcl : IsClosed ((decImage ℚ 2 A₀ : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    ((isClosed_Dec (F := ℚ) A₀).isCompact.image (continuous_cycZ ℚ Ω 2)).isClosed
  obtain ⟨h0, hle⟩ := idxAdic (decImage ℚ 2 A₀) (cycZ ℚ Ω 2 g) p c hcl ⟨g, hg, rfl⟩ hu hc
  have e : (cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀ = (decImage ℚ 2 A₀).comap (cycZ ℚ Ω 2) := by
    rw [decImage, Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : (decImage ℚ 2 A₀).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  refine ⟨fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hrel0).trans ?_
  rwa [Subgroup.relIndex_top_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.EmbedQZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem embQ_smul (l : ℕ) [Fact l.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (z : ℤ_[l]) (x : M)
    (hx : (l : ℤ_[l]) • x = 0) : z • x = z.zmodRepr • x := by
  have hm := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  calc z • x = (z - (z.zmodRepr : ℤ_[l])) • x + (z.zmodRepr : ℤ_[l]) • x := by
        rw [sub_smul, sub_add_cancel]
    _ = z.zmodRepr • x := by
        rw [← hb, mul_smul, hx, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]

private theorem embQ_fl (l : ℕ) [hl : Fact l.Prime] (T : Type) [AddCommGroup T] (r : ℕ) (hTn : ∀ x : T, l • x = 0)
    (hcard : CardLe T (l ^ r)) : ∃ g : T →+ (Fin r → ZMod l), Function.Injective g := by
  obtain ⟨hfin, hc⟩ := hcard
  letI : Module (ZMod l) T := AddCommGroup.zmodModule hTn
  haveI := Fintype.ofFinite T
  haveI hF : Module.Finite (ZMod l) T := Module.Finite.of_finite
  haveI hFr : Module.Free (ZMod l) T := Module.Free.of_divisionRing (ZMod l) T
  set d := Module.finrank (ZMod l) T with hd_def
  have hcardT : Fintype.card T = l ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod l) (V := T), ZMod.card]
  have hd : d ≤ r := by
    have : l ^ d ≤ l ^ r := by rw [← hcardT, ← Nat.card_eq_fintype_card]; exact hc
    exact (Nat.pow_le_pow_iff_right hl.out.one_lt).mp this
  let b := @Module.finBasis (ZMod l) T _ _ _ hFr _ hF
  let E := b.equivFun
  have hadd : ∀ s t : T, E.toFun (s + t) = E.toFun s + E.toFun t := E.map_add'
  have hzero : E.toFun 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    exact left_eq_add.mp this
  let g : T →+ (Fin r → ZMod l) :=
    { toFun := fun t i => if h : (i : ℕ) < d then E.toFun t ⟨i, h⟩ else 0
      map_zero' := by
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hzero, Pi.zero_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.zero_apply]
      map_add' := by
        intro s t
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hadd, Pi.add_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply, add_zero] }
  refine ⟨g, ?_⟩
  intro s t hst
  have key : E.toFun s = E.toFun t := by
    funext j
    have := congr_fun hst (Fin.castLE hd j)
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.coe_castLE, Fin.eta] at this
    rwa [dif_pos j.isLt, dif_pos j.isLt] at this
  calc s = E.invFun (E.toFun s) := (E.left_inv s).symm
    _ = E.invFun (E.toFun t) := by rw [key]
    _ = t := E.left_inv t

theorem UpperTheory.V.Two.embedQZ :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      ∃ f : D →ₗ[ℤ_[l]] (Fin r → QZ l), Function.Injective f := by
  intro l _ D _ _ r htors hcard
  set Tl := Submodule.torsionBy ℤ_[l] D (l : ℤ_[l]) with hTl
  have hTl' : ∀ t : Tl, (l : ℤ_[l]) • t = 0 := by
    intro t
    have h := t.2
    rw [Submodule.mem_torsionBy_iff] at h
    exact Subtype.ext h
  have hTn : ∀ t : Tl, l • t = 0 := by
    intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    exact hTl' t
  obtain ⟨g, hg⟩ := embQ_fl l Tl r hTn hcard
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let e : ZMod l ≃+* ZMod (l ^ 1) := ZMod.ringEquivCongr (pow_one l).symm
  have hιl : ∀ a, (l : ℤ_[l]) • ι a = 0 := by
    intro a
    have := (hιrange (ι a)).mp ⟨a, rfl⟩
    simpa using this
  let ψ : Fin r → Tl →+ QZ l := fun i =>
    ((ι : ZMod (l ^ 1) →+ QZ l).comp e.toAddMonoidHom).comp ((Pi.evalAddMonoidHom (fun _ => ZMod l) i).comp g)
  have hψl : ∀ i t, (l : ℤ_[l]) • ψ i t = 0 := fun i t => hιl _
  let ψL : Fin r → Tl →ₗ[ℤ_[l]] QZ l := fun i =>
    { toFun := ψ i
      map_add' := (ψ i).map_add
      map_smul' := by
        intro z t
        simp only [RingHom.id_apply]
        rw [embQ_smul l z t (hTl' t), map_nsmul, ← embQ_smul l z (ψ i t) (hψl i t)] }
  have hext := fun i => (UpperTheory.V.PropA.qzInj l).out Tl.subtype Subtype.val_injective (ψL i)
  choose y hy using hext
  refine ⟨LinearMap.pi y, ?_⟩
  have hzeroT : ∀ t : Tl, (∀ i, y i t = 0) → t = 0 := by
    intro t ht
    have hgt : g t = 0 := by
      funext i
      have h1 := hy i t
      rw [Submodule.coe_subtype, ht i] at h1
      have h2 : ι (e (g t i)) = ι 0 := by
        rw [map_zero]
        exact h1.symm
      have h3 := hιinj h2
      simpa using h3
    exact hg (by rw [hgt, map_zero])
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hxi : ∀ x : D, LinearMap.pi y x = 0 → ∀ i, y i x = 0 := by
    intro x hx i
    have := congr_fun hx i
    simpa using this
  obtain ⟨k, hk⟩ := htors x
  induction k generalizing x with
  | zero =>
    simpa using hk
  | succ k ih =>
    have hlx : (l : ℤ_[l]) • x = 0 := by
      apply ih ((l : ℤ_[l]) • x)
      · rw [map_smul, hx, smul_zero]
      · rw [← mul_smul, ← pow_succ]
        exact hk
    have hmem : x ∈ Tl := (Submodule.mem_torsionBy_iff _ _).mpr hlx
    have := hzeroT ⟨x, hmem⟩ (hxi x hx)
    simpa using congrArg Subtype.val this
end

