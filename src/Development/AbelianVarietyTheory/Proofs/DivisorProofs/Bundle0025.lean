module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountSpanSingletonEqMul
section
open NumberField IsDedekindDomain

namespace GlobalTheory.RootIdeal

theorem exists_pow_eq_spanSingleton (K : Type) [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    ∃ (h : ℕ) (x : K), 0 < h ∧ x ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x = J ^ h := by
  classical
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 J hJ
  have hpos : 0 < orderOf (ClassGroup.mk K u) := orderOf_pos _
  have h1 : ClassGroup.mk K (u ^ orderOf (ClassGroup.mk K u)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := h1.principal
  have hJh : ((u ^ orderOf (ClassGroup.mk K u) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = J ^ orderOf (ClassGroup.mk K u) := by
    simp [u]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x =
      J ^ orderOf (ClassGroup.mk K u) := by
    rw [← hJh]
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, hx]
  refine ⟨_, x, hpos, ?_, key⟩
  rintro rfl
  rw [FractionalIdeal.spanSingleton_zero] at key
  exact pow_ne_zero _ hJ key.symm

theorem exists_count_spanSingleton_eq_mul (K : Type) [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 K) →₀ ℚ) :
    ∃ (n : ℕ) (x : K), 0 < n ∧ x ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) : ℤ) : ℚ) = n * r v := by
  classical
  set d : ℕ := ∏ v ∈ r.support, (r v).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun v _ => (r v).pos)
  have hdvd : ∀ v, (r v).den ∣ d := by
    intro v
    by_cases hv : v ∈ r.support
    · exact Finset.dvd_prod_of_mem _ hv
    · rw [Finsupp.notMem_support_iff.mp hv]
      simp
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    Finsupp.mapRange (fun q : ℚ => q.num * ((d / q.den : ℕ) : ℤ)) (by simp) r
  have he : ∀ v, ((e v : ℤ) : ℚ) = d * r v := by
    intro v
    simp only [e, Finsupp.mapRange_apply]
    have hden : ((r v).den : ℚ) ≠ 0 := by exact_mod_cast (r v).pos.ne'
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hdvd v) hden]
    conv_rhs => rw [← Rat.num_div_den (r v)]
    field_simp
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    e.prod (fun v n => ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)
    with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count K v J = e v := fun v =>
    FractionalIdeal.count_finsuppProd K v e
  obtain ⟨h, x, hh, hx0, hxJ⟩ := exists_pow_eq_spanSingleton K J hJ0
  refine ⟨h * d, x, Nat.mul_pos hh hdpos, hx0, fun v => ?_⟩
  rw [hxJ, FractionalIdeal.count_pow, hcount, Int.cast_mul, Int.cast_natCast, he]
  push_cast
  ring

end GlobalTheory.RootIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqOneOfPowMem
section
open TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_derivation_eq_one_of_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (L : Subfield K) (f : K), f ∉ L → f ^ p ∈ L → IntermediateField.adjoin L ({f} : Set K) = ⊤ → ∃ D : Derivation L K K, D f = 1 := by
  intro p hp K _ _ L f hfL hfp htop
  have hpp : p.Prime := hp.out
  set a : L := ⟨f ^ p, hfp⟩ with ha
  set q : Polynomial L := X ^ p - C a with hq
  have hqf : aeval f q = 0 := by
    rw [hq, map_sub, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr rfl
  have hirr : Irreducible q := by
    apply X_pow_sub_C_irreducible_of_prime hpp
    intro b hb
    apply hfL
    have h1 : (b : K) ^ p = f ^ p := by
      have := congrArg (fun x : L => (x : K)) hb
      simpa [a] using this
    have h2 : (b : K) = f := frobenius_inj K p h1
    exact h2 ▸ b.2
  have hmon : q.Monic := monic_X_pow_sub_C a hpp.ne_zero
  have hmin : minpoly L f = q := (minpoly.eq_of_irreducible_of_monic hirr hqf hmon).symm
  have hdq : aeval f (derivative q) = 0 := by
    simp [q, derivative_X_pow]
  have hker : ∀ g : Polynomial L, aeval f g = 0 → aeval f (derivative g) = 0 := by
    intro g hg
    obtain ⟨h, rfl⟩ : q ∣ g := hmin ▸ minpoly.dvd L f hg
    simp [derivative_mul, hdq, hqf]
  have hint : IsIntegral L f := ⟨q, hmon, hqf⟩
  have hsurj : ∀ x : K, ∃ g : Polynomial L, aeval f g = x := by
    intro x
    have hx : x ∈ Algebra.adjoin L ({f} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).mp hx
  choose G hG using hsurj
  have hwd : ∀ g1 g2 : Polynomial L, aeval f g1 = aeval f g2 →
      aeval f (derivative g1) = aeval f (derivative g2) := by
    intro g1 g2 h
    have := hker (g1 - g2) (by rw [map_sub, h, sub_self])
    rwa [derivative_sub, map_sub, sub_eq_zero] at this
  let Dl : K →ₗ[L] K :=
    { toFun := fun x => aeval f (derivative (G x))
      map_add' := fun x y => by
        rw [← map_add (f := _), ← derivative_add]
        apply hwd
        rw [hG, map_add (f := _), hG, hG]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← map_smul (aeval f), ← map_smul derivative]
        apply hwd
        rw [hG, map_smul, hG] }
  refine ⟨Derivation.mk' Dl (fun x y => ?_), ?_⟩
  · show aeval f (derivative (G (x * y))) = x • aeval f (derivative (G y)) + y • aeval f (derivative (G x))
    rw [hwd (G (x * y)) (G x * G y) (by rw [hG, map_mul, hG, hG]), derivative_mul, map_add (f := _), map_mul, map_mul, hG, hG, smul_eq_mul, smul_eq_mul]
    ring
  · show aeval f (derivative (G f)) = 1
    rw [hwd (G f) X (by rw [hG, aeval_X]), derivative_X, map_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentForm
section
open IsLocalRing

namespace GlobalTheory.ConormalDer

theorem exists_derivation_cotangent (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by
  set m := maximalIdeal B with hm
  let π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha =>
      (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a := fun _ => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨_, hπ a⟩
  have hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)
  have hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]
    exact Ideal.pow_right_mono (fun z hz => hker z hz) 2
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y
  have hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal := fun a =>
    hker _ (by rw [map_sub, hs, hπ, sub_self])
  let D : B → CotangentSpace B := fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩
  have hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a) :=
    fun a => by
      rw [← Ideal.cotangentEquivIdeal_apply]
      simp only [D, LinearEquiv.apply_symm_apply]
  have hinj := m.cotangentToQuotientSquare_injective
  have hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) *
      (Ideal.Quotient.mk _ b - s (residue B b)) = 0 := fun a b => by
    have := Ideal.mul_mem_mul (hmem a) (hmem b)
    rwa [← pow_two, m.cotangentIdeal_square, Ideal.mem_bot] at this
  have hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z := fun a z =>
    Algebra.smul_def a z
  have hmul : ∀ a b, D (a * b) = a • D b + b • D a := fun a b => by
    apply hinj
    rw [map_add (f := _), map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]
    linear_combination (-1 : B ⧸ m ^ 2) * hsq a b
  have hR : ∀ c : R, D (algebraMap R B c) = 0 := fun c => by
    apply hinj
    rw [hD, map_zero, sub_eq_zero]
    exact (s.commutes c).symm
  refine ⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩
  · apply hinj
    rw [map_add (f := _), hD, hD, hD, map_add (f := _), map_add (f := _), map_add (f := _)]
    ring
  · show D (c • a) = c • D a
    rw [Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]
  · apply hinj
    show m.cotangentToQuotientSquare (D t) = _
    rw [hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]
    rfl

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem formallySmooth_residueField (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by
  let K := FractionRing R
  have hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c) := fun c =>
    hu c (nonZeroDivisors.ne_zero c.2)
  letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra
  haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq hu' c).symm
  haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B,
      ← IsScalarTower.algebraMap_apply]
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _
  haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  exact .comp R K (ResidueField B)

theorem exists_derivation_extending :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  intro R B _ _ _ _ _ _ hu lam
  haveI := formallySmooth_residueField R B hu
  obtain ⟨D, hmul, hD⟩ := exists_derivation_cotangent R B
  have hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v := fun a v => by
    rw [← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]
  let L : B →ₗ[R] ResidueField B :=
    { toFun := fun a => lam (D a)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }
  refine ⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩
  · change lam (D (a * b)) = a • lam (D b) + b • lam (D a)
    rw [hmul, map_add (f := _), hsm, hsm]
  · show lam (D y) = _
    exact congrArg lam (hD ⟨y, hy⟩)

end GlobalTheory.ConormalDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLifting
section
namespace GlobalTheory.LiftDeriv

theorem krullDimLE_and_isLocalRing_quotient {P : Type} [CommRing P] (Q S : Ideal P) [hQ : Q.IsMaximal]
    (n : ℕ) (h1 : Q ^ (n + 1) ≤ S) (h2 : S ≤ Q) :
    Ring.KrullDimLE 0 (P ⧸ S) ∧ IsLocalRing (P ⧸ S) := by
  have hSt : S ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.1 (h ▸ h2))
  have : Nontrivial (P ⧸ S) := Ideal.Quotient.nontrivial_iff.2 hSt
  have key : ∀ M : Ideal (P ⧸ S), M.IsPrime → M = Q.map (Ideal.Quotient.mk S) := by
    intro M hM
    have hc : (M.comap (Ideal.Quotient.mk S)).IsPrime := Ideal.comap_isPrime _ _
    have h3 : Q ≤ M.comap (Ideal.Quotient.mk S) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (h1 ha)]
      exact M.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M).symm.trans
      (congrArg _ (hQ.eq_of_le hc.ne_top h3).symm)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (P ⧸ S)
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (P ⧸ S)).out 2 1 rfl rfl).mp
    ⟨M, hM.isPrime, fun M' hM' => (key M' hM').trans (key M hM.isPrime).symm⟩

theorem exists_derivation_extending : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hg hlift ℓ
  have hPK : algebraMap P K = (algebraMap R K).comp (algebraMap P R) := IsScalarTower.algebraMap_eq P R K
  have hQm : (RingHom.ker (algebraMap P K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (by rw [hPK]; exact hg.comp hf)
  have hIQ : RingHom.ker (algebraMap P R) ≤ RingHom.ker (algebraMap P K) := fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [hPK, RingHom.comp_apply, hx, map_zero]
  generalize hI : RingHom.ker (algebraMap P R) = I at ℓ hIQ
  generalize hQ : RingHom.ker (algebraMap P K) = Q at hQm hIQ
  let J : Ideal P := Submodule.map I.subtype (LinearMap.ker ℓ)
  have hJI : J ≤ I := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hJ : ∀ (i i' : P) (hi : i ∈ I) (hi' : i' ∈ I), i' - i ∈ J → ℓ ⟨i, hi⟩ = ℓ ⟨i', hi'⟩ := by
    intro i i' hi hi' h
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h
    have e : x = ⟨i', hi'⟩ - ⟨i, hi⟩ := Subtype.ext (by simpa using hxe)
    rw [LinearMap.mem_ker, e, map_sub, sub_eq_zero] at hx
    exact hx.symm
  have hQIJ : Q * I ≤ J := by
    refine Ideal.mul_le.2 fun q hq i hi => ?_
    refine Submodule.mem_map.2 ⟨⟨q * i, I.mul_mem_left q hi⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    have e : (⟨q * i, I.mul_mem_left q hi⟩ : I) = q • ⟨i, hi⟩ := rfl
    rw [e, map_smul, Algebra.smul_def]
    have hq0 : algebraMap P K q = 0 := by rw [← RingHom.mem_ker, hQ]; exact hq
    rw [hq0, zero_mul]
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul Q (I : Submodule P P)
  have hAR : Q ^ (k + 1) ⊓ I ≤ J := by
    have h := hk (k + 1) (Nat.le_succ k)
    rw [Nat.add_sub_cancel_left, pow_one] at h
    have e : (Q ^ (k + 1) • ⊤ : Submodule P P) = Q ^ (k + 1) := by rw [smul_eq_mul, Ideal.mul_top]
    rw [e] at h
    rw [h]
    exact le_trans (Submodule.smul_mono le_rfl inf_le_right) hQIJ

  let S : Ideal P := J ⊔ Q ^ (k + 1)
  let T : Ideal P := I ⊔ Q ^ (k + 1)
  have hST : S ≤ T := sup_le_sup_right hJI _
  have hSQ : S ≤ Q := sup_le (hJI.trans hIQ) (Ideal.pow_le_self (Nat.succ_ne_zero k))
  obtain ⟨hdim, hloc⟩ := krullDimLE_and_isLocalRing_quotient Q S k le_sup_right hSQ
  haveI : IsArtinianRing (P ⧸ S) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let π : P ⧸ S →+* P ⧸ T := Ideal.Quotient.factor hST
  have hπmk : ∀ x, π (Ideal.Quotient.mk S x) = Ideal.Quotient.mk T x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hπmk x⟩
  have hTT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ S := by
    intro x hx y hy
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨i', hi', z', hz', rfl⟩ := Submodule.mem_sup.1 hy
    have e : (i + z) * (i' + z') = i * i' + (i * z' + z * (i' + z')) := by ring
    rw [e]
    refine S.add_mem (Ideal.mem_sup_left (hQIJ (Ideal.mul_mem_mul (hIQ hi) hi'))) (Ideal.mem_sup_right ?_)
    exact (Q ^ (k + 1)).add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz)
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun c hc d hd => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [RingHom.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc hd
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hTT x hc y hd
  let β : A →+* P ⧸ S := (Ideal.Quotient.mk S).comp (algebraMap A P)
  have hIT : RingHom.ker (algebraMap P R) ≤ T := hI ▸ le_sup_left
  let e := RingHom.quotientKerEquivOfSurjective hf
  let L : P ⧸ RingHom.ker (algebraMap P R) →+* P ⧸ T :=
    Ideal.Quotient.lift (RingHom.ker (algebraMap P R)) (Ideal.Quotient.mk T)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hIT ha))
  let φ₀ : R →+* P ⧸ T := L.comp e.symm.toRingHom
  have hφ₀ : ∀ a, φ₀ (algebraMap P R a) = Ideal.Quotient.mk T a := by
    intro a
    have h1 : e.symm (algebraMap P R a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change L (e.symm (algebraMap P R a)) = _
    rw [h1, Ideal.Quotient.lift_mk]
  have hcomp : φ₀.comp (algebraMap A R) = π.comp β := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A P R r, hφ₀]
    rfl
  obtain ⟨φ, hφπ, hφA⟩ := hlift (P ⧸ S) (P ⧸ T) π hπs hsq β φ₀ hcomp

  let δ : P → P ⧸ S := fun a => Ideal.Quotient.mk S a - φ (algebraMap P R a)
  have hδ : ∀ a, δ a ∈ RingHom.ker π := by
    intro a
    rw [RingHom.mem_ker]
    show π (Ideal.Quotient.mk S a - φ (algebraMap P R a)) = 0
    rw [map_sub, hπmk, ← RingHom.comp_apply, hφπ, hφ₀, sub_self]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b
    show Ideal.Quotient.mk S (a + b) - φ (algebraMap P R (a + b)) = _
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    show _ = (Ideal.Quotient.mk S a - φ (algebraMap P R a)) + (Ideal.Quotient.mk S b - φ (algebraMap P R b))
    ring
  have hδmul : ∀ a b, δ (a * b) = Ideal.Quotient.mk S a * δ b + Ideal.Quotient.mk S b * δ a := by
    intro a b
    have h0 : δ a * δ b = 0 := by
      have : δ a * δ b ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hδ a) (hδ b)
      rw [hsq] at this
      exact (Ideal.mem_bot.1 this)
    change (Ideal.Quotient.mk S a - φ (algebraMap P R a)) * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) = 0 at h0
    show Ideal.Quotient.mk S (a * b) - φ (algebraMap P R (a * b)) =
      Ideal.Quotient.mk S a * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) +
        Ideal.Quotient.mk S b * (Ideal.Quotient.mk S a - φ (algebraMap P R a))
    rw [map_mul, map_mul, map_mul]
    linear_combination -h0

  let Rl : P ⧸ S → K → Prop := fun c v => ∃ (i : P) (hi : i ∈ I), ∃ z ∈ Q ^ (k + 1),
    Ideal.Quotient.mk S (i + z) = c ∧ ℓ ⟨i, hi⟩ = v
  have huniq : ∀ c v v', Rl c v → Rl c v' → v = v' := by
    rintro c v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', he, rfl⟩
    rw [Ideal.Quotient.eq] at he
    obtain ⟨j, hj, w, hw, hjw⟩ := Submodule.mem_sup.1 he
    have hmem : i' - i - j ∈ Q ^ (k + 1) ⊓ I := by
      refine ⟨?_, (I.sub_mem (I.sub_mem hi' hi) (hJI hj))⟩
      have e1 : i' - i - j = w + z - z' := by linear_combination -hjw
      rw [e1]
      exact (Q ^ (k + 1)).sub_mem ((Q ^ (k + 1)).add_mem hw hz) hz'
    have h2 : i' - i ∈ J := by
      have := J.add_mem (hAR hmem) hj
      rwa [sub_add_cancel] at this
    exact hJ i i' hi hi' h2
  have hex : ∀ c : P ⧸ S, π c = 0 → ∃ v, Rl c v := by
    intro c hc
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    exact ⟨_, i, hi, z, hz, rfl, rfl⟩
  have hRadd : ∀ c c' v v', Rl c v → Rl c' v' → Rl (c + c') (v + v') := by
    rintro c c' v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', rfl, rfl⟩
    refine ⟨i + i', I.add_mem hi hi', z + z', (Q ^ (k + 1)).add_mem hz hz', ?_, ?_⟩
    · rw [← map_add (f := _)]; congr 1; ring
    · rw [← map_add (f := _)]; rfl
  have hRsmul : ∀ c v (p : P), Rl c v → Rl (Ideal.Quotient.mk S p * c) (p • v) := by
    rintro c v p ⟨i, hi, z, hz, rfl, rfl⟩
    refine ⟨p * i, I.mul_mem_left p hi, p * z, Ideal.mul_mem_left _ p hz, ?_, ?_⟩
    · rw [← map_mul]; congr 1; ring
    · rw [← map_smul]; rfl
  have hR0 : Rl 0 0 := ⟨0, I.zero_mem, 0, (Q ^ (k + 1)).zero_mem, by simp, map_zero ℓ⟩
  have hRI : ∀ i (hi : i ∈ I), Rl (Ideal.Quotient.mk S i) (ℓ ⟨i, hi⟩) :=
    fun i hi => ⟨i, hi, 0, (Q ^ (k + 1)).zero_mem, by rw [add_zero], rfl⟩
  let D0 : P → K := fun a => Classical.choose (hex (δ a) (hδ a))
  have hD0 : ∀ a v, Rl (δ a) v → D0 a = v := fun a v h =>
    huniq _ _ _ (Classical.choose_spec (hex (δ a) (hδ a))) h
  have hspec : ∀ a, Rl (δ a) (D0 a) := fun a => Classical.choose_spec (hex (δ a) (hδ a))
  have hDadd : ∀ a b, D0 (a + b) = D0 a + D0 b := fun a b =>
    hD0 _ _ (by rw [hδadd]; exact hRadd _ _ _ _ (hspec a) (hspec b))
  have hDmul : ∀ a b, D0 (a * b) = a • D0 b + b • D0 a := fun a b =>
    hD0 _ _ (by rw [hδmul]; exact hRadd _ _ _ _ (hRsmul _ _ a (hspec b)) (hRsmul _ _ b (hspec a)))
  have hDA : ∀ r : A, D0 (algebraMap A P r) = 0 := by
    intro r
    refine hD0 _ _ ?_
    have : δ (algebraMap A P r) = 0 := by
      show Ideal.Quotient.mk S (algebraMap A P r) - φ (algebraMap P R (algebraMap A P r)) = 0
      rw [← IsScalarTower.algebraMap_apply A P R r, ← RingHom.comp_apply φ, hφA, sub_eq_zero]
      rfl
    rw [this]; exact hR0
  let Dl : P →ₗ[A] K :=
    { toFun := D0
      map_add' := hDadd
      map_smul' := fun r a => by
        rw [Algebra.smul_def, hDmul, hDA, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' Dl hDmul, fun ⟨i, hi⟩ => ?_⟩
  show D0 i = ℓ ⟨i, hi⟩
  refine hD0 _ _ ?_
  have : δ i = Ideal.Quotient.mk S i := by
    show Ideal.Quotient.mk S i - φ (algebraMap P R i) = _
    have hi0 : algebraMap P R i = 0 := by rw [← RingHom.mem_ker, hI]; exact hi
    rw [hi0, map_zero, sub_zero]
  rw [this]; exact hRI i hi

end GlobalTheory.LiftDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSource
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_factor_closedImmersion_of_locally :
    ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z),
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) →
      ∃ z : Y ⟶ A, z ≫ a = g := by
  intro Z A Y a ha g h
  choose W hW z hz using h
  have hc : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover W hc
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, 𝒰.X i ⟶ A, ∀ i, u i ≫ a = 𝒰.f i ≫ g := ⟨z, hz⟩
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    rw [← cancel_mono a, Category.assoc, Category.assoc, hu, hu, pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms u hglue, ?_⟩
  refine 𝒰.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact hu i

end GlobalTheory
end

