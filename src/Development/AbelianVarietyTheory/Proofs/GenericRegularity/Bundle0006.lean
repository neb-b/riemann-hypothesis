module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
section
namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem exists_integral_point_through (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (M : Ideal B) (hM : M.IsMaximal) (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ M)
    (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ maximalIdeal V := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  set w := algebraMap O B ϖ with hw

  have hw0 : w ≠ 0 := by
    intro h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have h1 : ϖ • (1 : B) = ϖ • (0 : B) := by rw [Algebra.smul_def, mul_one, ← hw, h0, smul_zero]
    exact one_ne_zero (hreg h1)
  have hϖm : ϖ ∈ maximalIdeal O := by rw [hmO]; exact Ideal.mem_span_singleton_self ϖ
  have hwM : w ∈ M := hsp (Ideal.mem_map_of_mem _ hϖm)
  obtain ⟨q, hq, hqM, heq, hwq, hchain⟩ := DimensionQuotientBound.local_step M w e hwM hw0 he
  obtain ⟨s, hsM, hs⟩ := PrimeAvoidanceFibre.avoid M q w hchain

  let D := B ⧸ q
  have : IsDomain D := Ideal.Quotient.isDomain q
  let sb : D := Ideal.Quotient.mk q s
  have hsb : sb ≠ 0 := fun h => hsM (hqM (Ideal.Quotient.eq_zero_iff_mem.1 h))
  let D' := Localization.Away sb
  have hpow : Submonoid.powers sb ≤ nonZeroDivisors D := powers_le_nonZeroDivisors_of_noZeroDivisors hsb
  have : IsDomain D' := IsLocalization.isDomain_localization hpow
  have : IsNoetherianRing D' := IsLocalization.isNoetherianRing (Submonoid.powers sb) D' inferInstance
  have : Algebra.FiniteType O D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType O D' := inferInstance
  have hDinj : Function.Injective (algebraMap D D') := IsLocalization.injective D' hpow

  let f : B →+* D' := (algebraMap D D').comp (Ideal.Quotient.mk q)
  have hfO : ∀ c : O, algebraMap O D' c = f (algebraMap O B c) := fun c => by
    rw [IsScalarTower.algebraMap_apply O D D']; rfl
  have hcomapM : ∀ P : Ideal D', P.IsPrime → algebraMap O D' ϖ ∈ P → Ideal.comap f P = M := by
    intro P hP hwP
    refine hs _ (Ideal.comap_isPrime f P) (fun x hx => ?_) ?_ ?_
    · show algebraMap D D' (Ideal.Quotient.mk q x) ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]; exact P.zero_mem
    · rw [Ideal.mem_comap, ← hfO]; exact hwP
    · intro hsP
      have hu : IsUnit (algebraMap D D' sb) := IsLocalization.map_units D' ⟨sb, Submonoid.mem_powers sb⟩
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsP hu)
  have huniq : ∀ P P' : Ideal D', P.IsPrime → P'.IsPrime → algebraMap O D' ϖ ∈ P →
      algebraMap O D' ϖ ∈ P' → P = P' := by
    intro P P' hP hP' hwP hwP'
    have e1 : Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P) =
        Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P') := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      exact (hcomapM P hP hwP).trans (hcomapM P' hP' hwP').symm
    have e2 := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e1
    rw [← IsLocalization.map_under (Submonoid.powers sb) D' P,
      ← IsLocalization.map_under (Submonoid.powers sb) D' P']
    exact congrArg _ e2
  have hex : ∃ P : Ideal D', P.IsPrime ∧ algebraMap O D' ϖ ∈ P := by
    let Mb := Ideal.map (Ideal.Quotient.mk q) M
    have hMb : Mb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
    have hcMb : Ideal.comap (Ideal.Quotient.mk q) Mb = M := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hqM]
    have hdisj : Disjoint (Submonoid.powers sb : Set D) Mb := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      have : s ^ n ∈ M := by
        rw [← hcMb, Ideal.mem_comap, map_pow]; exact hx
      exact hsM (hM.isPrime.mem_of_pow_mem n this)
    refine ⟨Ideal.map (algebraMap D D') Mb,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers sb) D' Mb hMb hdisj, ?_⟩
    rw [hfO]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)
  have hfin : Module.Finite O D' := PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ hex huniq

  have hOinj : Function.Injective (algebraMap O D') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    by_contra hne
    push Not at hne
    obtain ⟨c, hc, hc0⟩ := hne
    have hker : RingHom.ker (algebraMap O D') ≠ ⊥ := fun h =>
      hc0 ((RingHom.injective_iff_ker_eq_bot _).2 h (hc.trans (map_zero _).symm))
    have hkp : (RingHom.ker (algebraMap O D')).IsPrime := RingHom.ker_isPrime _
    have hkm : RingHom.ker (algebraMap O D') = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (hkp.isMaximal hker)
    have hϖk : ϖ ∈ RingHom.ker (algebraMap O D') := by
      rw [hkm, hmO]; exact Ideal.mem_span_singleton_self ϖ
    rw [RingHom.mem_ker, hfO] at hϖk
    apply hwq
    have : algebraMap D D' (Ideal.Quotient.mk q w) = algebraMap D D' 0 := by rw [map_zero]; exact hϖk
    exact Ideal.Quotient.eq_zero_iff_mem.1 (hDinj this)
  have : FaithfulSMul O D' := (faithfulSMul_iff_algebraMap_injective O D').2 hOinj

  let K := FractionRing O
  let L := FractionRing D'
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 (by
    rw [IsScalarTower.algebraMap_eq O D' L]
    exact (IsFractionRing.injective D' L).comp hOinj)
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : Algebra.IsIntegral O D' := Algebra.IsIntegral.of_finite O D'
  have : FiniteDimensional K L := Module.Finite.of_isLocalization O D' (nonZeroDivisors O)
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  have : Algebra.IsSeparable K L := inferInstance
  have hVfin : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L (integralClosure O L)
  have hdvr : IsDiscreteValuationRing (integralClosure O L) := FiniteAlgebraLocalCompletion.cl_dvr O K L

  let g1 : B →ₐ[O] D := Ideal.Quotient.mkₐ O q
  let g2 : D →ₐ[O] D' := IsScalarTower.toAlgHom O D D'
  let g3 : D' →ₐ[O] L := IsScalarTower.toAlgHom O D' L
  let g4 : D' →ₐ[O] integralClosure O L :=
    g3.codRestrict (integralClosure O L) fun x => (Algebra.IsIntegral.isIntegral x).map g3
  refine ⟨integralClosure O L, inferInstance, inferInstance, hdvr, inferInstance, hVfin,
    g4.comp (g2.comp g1), ?_, ?_⟩
  swap
  ·
    have hloc := FiniteAlgebraLocalCompletion.cl_isLocalHom O L
    let P : Ideal D' := Ideal.comap g4 (maximalIdeal (integralClosure O L))
    have hP : P.IsPrime := Ideal.comap_isPrime _ _
    have hϖP : algebraMap O D' ϖ ∈ P := by
      show g4 (algebraMap O D' ϖ) ∈ maximalIdeal (integralClosure O L)
      rw [g4.commutes]
      exact map_nonunit _ ϖ hϖm
    intro x hx
    rw [← hcomapM P hP hϖP] at hx
    exact hx
  intro h0
  have h1 : g3 (g2 (g1 e)) = 0 := congrArg Subtype.val h0
  have h2 : g2 (g1 e) = 0 := (IsFractionRing.injective D' L) (h1.trans (map_zero _).symm)
  have h3 : g1 e = 0 := hDinj (h2.trans (map_zero _).symm)
  exact heq (Ideal.Quotient.eq_zero_iff_mem.1 h3)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnramifiedExtension
section
open TensorProduct

namespace GlobalTheory.DVRBaseChange

theorem exists_dvr_quotient (W : Type) [CommRing W] [IsLocalRing W] (π : W)
    (hm : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ : ¬ IsNilpotent π) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : W →+* V), Irreducible (q π) := by
  classical
  have hnu : ∀ x : W, ¬ IsUnit x ↔ π ∣ x := fun x => by
    rw [← Ideal.mem_span_singleton, ← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let J : Ideal W := ⨅ n : ℕ, Ideal.span {π ^ n}
  have hJ : ∀ x, x ∈ J ↔ ∀ n : ℕ, π ^ n ∣ x := fun x => by
    simp only [J, Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hpow : ∀ n : ℕ, π ^ n ∉ J := by
    intro n hn
    obtain ⟨y, hy⟩ := (hJ _).1 hn (n + 1)
    have hu : IsUnit (1 - π * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((hnu _).2 (dvd_mul_right _ _))
    refine hπ ⟨n, ?_⟩
    have : π ^ n * (1 - π * y) = 0 := by linear_combination hy
    exact (hu.mul_left_eq_zero).1 this
  have hfac : ∀ x, x ∉ J → ∃ (n : ℕ) (u : W), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra hc
      push Not at hc
      exact hx ((hJ x).2 fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (hc n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · by_contra hc
        exact Nat.find_min hex (m := m) (by omega) hc
    obtain ⟨u, hu⟩ := h1
    refine ⟨_, u, ?_, hu⟩
    by_contra hc
    obtain ⟨v, rfl⟩ := (hnu u).1 hc
    exact Nat.find_spec hex ⟨v, hu.trans (by ring)⟩
  have hprime : J.IsPrime := by
    refine ⟨fun h => hpow 0 (h ▸ Submodule.mem_top), fun {x y} hxy => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨n, u, hu, rfl⟩ := hfac x hc.1
    obtain ⟨m, v, hv, rfl⟩ := hfac y hc.2
    refine hpow (n + m) ?_
    rw [← J.mul_unit_mem_iff_mem (hu.mul hv)]
    convert hxy using 1
    ring
  have hdom : IsDomain (W ⧸ J) := Ideal.Quotient.isDomain J
  have hloc : IsLocalRing (W ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hirr : Irreducible (Ideal.Quotient.mk J π) := by
    refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ ?_
    · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hpow 1
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_singleton]
  refine ⟨W ⧸ J, inferInstance, hdom,
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩,
    Ideal.Quotient.mk J, hirr⟩
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, u, hu, rfl⟩ := hfac x (fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h))
  refine ⟨n, ?_⟩
  rw [map_mul, map_pow]
  exact associated_mul_unit_right _ _ (hu.map _)

theorem exists_dvr_of_isRadical (S : Type) [CommRing S] (π : S)
    (hrad : (Ideal.span {π}).IsRadical) (hne : Ideal.span {π} ≠ ⊤)
    (hreg : ∀ s, π * s = 0 → s = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : S →+* V), Irreducible (q π) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  let W := Localization.AtPrime p
  have hm : IsLocalRing.maximalIdeal W = Ideal.span {algebraMap S W π} := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes W p _ hp
    rw [← IsLocalization.map_radical p.primeCompl, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton] at h1
    exact h1.symm
  have hn : ¬ IsNilpotent (algebraMap S W π) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl] at hn
    obtain ⟨⟨s, hs⟩, h⟩ := hn
    have key : ∀ (n : ℕ) (s : S), s * π ^ n = 0 → s = 0 := by
      intro n
      induction n with
      | zero => intro s h; simpa using h
      | succ n ih => intro s h; exact ih s (hreg _ (by linear_combination h))
    exact hs (by rw [key n s h]; exact p.zero_mem)
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_quotient W _ hm hn
  exact ⟨V, i1, i2, i3, q.comp (algebraMap S W), hq⟩

theorem exists_unramified_extension :
    ∀ (K F T : Type) [Field K] [CharZero K] [Field F] [Algebra K F] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra K T], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (i : T →+* V) (χ : F →+* V), Function.Injective i ∧ (∀ ϖ : T, Irreducible ϖ → Irreducible (i ϖ)) ∧ IsLocalHom i ∧ ∀ a : K, i (algebraMap K T a) = χ (algebraMap K F a) := by
  intro K F T _ _ _ _ _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  let m := IsLocalRing.maximalIdeal T
  have hm : m = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  let g : T ⊗[K] F →ₐ[K] (T ⧸ m) ⊗[K] F :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K F)
  have hker : RingHom.ker g = Ideal.span {ϖ ⊗ₜ[K] (1 : F)} := by
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective K m)]
    have : RingHom.ker (Ideal.Quotient.mkₐ K m) = Ideal.span {ϖ} := by
      rw [← hm]; exact Ideal.mk_ker
    rw [this, Ideal.map_span, Set.image_singleton]
    rfl
  have hred : IsReduced ((T ⧸ m) ⊗[K] F) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  have hrad : (Ideal.span {ϖ ⊗ₜ[K] (1 : F)}).IsRadical := by
    rw [← hker]
    exact Ideal.isRadical_bot.comap _
  have hne : Ideal.span {ϖ ⊗ₜ[K] (1 : F)} ≠ ⊤ := by
    rw [← hker]
    exact RingHom.ker_ne_top _
  have hreg : ∀ s : T ⊗[K] F, (ϖ ⊗ₜ[K] (1 : F)) * s = 0 → s = 0 := by
    intro s hs
    have hinj : Function.Injective ((LinearMap.mulLeft K ϖ).rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun a b h => mul_left_cancel₀ hϖ.ne_zero h)
    have key : ∀ s : T ⊗[K] F, (LinearMap.mulLeft K ϖ).rTensor F s = (ϖ ⊗ₜ[K] (1 : F)) * s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add (f := _), hx, hy, mul_add]
    exact hinj (by rw [key, hs, map_zero])
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_of_isRadical _ _ hrad hne hreg
  let i : T →+* V := q.comp Algebra.TensorProduct.includeLeftRingHom
  have hi : Irreducible (i ϖ) := hq
  refine ⟨V, i1, i2, i3, i, q.comp (Algebra.TensorProduct.includeRight (R := K) (A := T)).toRingHom,
    ?_, ?_, ⟨?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map i).ne_zero (pow_ne_zero n hi.ne_zero) hx
  · intro ϖ' h'
    exact ((IsDiscreteValuationRing.associated_of_irreducible T hϖ h').map i).irreducible hi
  · intro x hx
    by_contra h0
    have : x ∈ m := h0
    rw [hm, Ideal.mem_span_singleton] at this
    exact hi.not_isUnit (isUnit_of_dvd_unit (map_dvd i this) hx)
  · intro a
    change q (algebraMap K T a ⊗ₜ[K] (1 : F)) = q ((1 : T) ⊗ₜ[K] algebraMap K F a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.DVRBaseChange
end

