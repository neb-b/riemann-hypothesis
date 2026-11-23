module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualField

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel Module

namespace PI.LocDualGen.EpG

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]

local notation "C" => integralClosure 𝒪[K] L

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem integralClosure_selfDual
    (hU : ∀ z : C, z * z ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      z ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) (x : L) :
    (∀ y ∈ C, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ C := by
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain 𝒪[K] K L
  haveI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Module.Finite 𝒪[K] C := IsIntegralClosure.finite 𝒪[K] K L C
  haveI : Module.IsTorsionFree 𝒪[K] C := by
    haveI := PI.LocDualGen.EpF.tf K L
    exact Subalgebra.instIsTorsionFree C
  haveI : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing C) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hdiff : differentIdeal 𝒪[K] C = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hP.isPrime
    apply (not_dvd_differentIdeal_iff (A := 𝒪[K]) (B := C) (P := P)).2 _
      (Ideal.dvd_iff_le.2 hle)
    have hpmax : (P.comap (algebraMap 𝒪[K] C)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    have hp : P.comap (algebraMap 𝒪[K] C) = 𝓂[K] := IsLocalRing.eq_maximalIdeal hpmax
    haveI : P.LiesOver 𝓂[K] := ⟨hp.symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver 𝓂[K] P
    rw [Algebra.isUnramifiedAt_iff_map_eq 𝒪[K] 𝓂[K] P]
    constructor
    · haveI : Finite (𝒪[K] ⧸ 𝓂[K]) := (inferInstance : Finite 𝓀[K])
      haveI : Finite 𝓂[K].ResidueField :=
        Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝓂[K]).2
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
    · have hP0 : P ≠ ⊥ := fun h => differentIdeal_ne_bot (le_bot_iff.1 (h ▸ hle))
      haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP0
        (Localization.AtPrime P)
      let J := Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]
      let Jₚ := J.map (algebraMap C (Localization.AtPrime P))
      have hmap : Jₚ = 𝓂[K].map (algebraMap 𝒪[K] (Localization.AtPrime P)) := by
        dsimp only [Jₚ, J]
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have hrad : J.IsRadical := (Ideal.isRadical_iff_pow_one_lt (I := J) 2 (by decide)).2
        (by simpa only [sq] using hU)
      have hradₚ : Jₚ.radical = Jₚ := by
        rw [← IsLocalization.map_radical P.primeCompl, hrad.radical]
      have hleₚ : Jₚ ≤ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 hp.ge)
      have hinj : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
        IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
      have hinjO : Function.Injective (algebraMap 𝒪[K] (Localization.AtPrime P)) := by
        rw [IsScalarTower.algebraMap_eq 𝒪[K] C (Localization.AtPrime P)]
        exact hinj.comp (FaithfulSMul.algebraMap_injective 𝒪[K] C)
      have hJₚ0 : Jₚ ≠ ⊥ := by
        rw [hmap, Ne, Ideal.map_eq_bot_iff_of_injective hinjO]
        exact IsDiscreteValuationRing.not_a_field _
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
      obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJₚ0 hπ
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (by simpa [hn] using hleₚ))
      have hmaxrad : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsRadical :=
        Ideal.IsPrime.isRadical inferInstance
      rw [← hmap, ← hradₚ, hn, ← Ideal.span_singleton_pow, Ideal.radical_pow _ hn0,
        ← hπ.maximalIdeal_eq, hmaxrad.radical]
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal (nonZeroDivisors C) L) = 1 := by
    have h := coeIdeal_differentIdeal 𝒪[K] K L C
    rw [hdiff, FractionalIdeal.coeIdeal_top] at h
    exact inv_eq_one.1 h.symm
  have hmem (z : L) : z ∈ (1 : FractionalIdeal (nonZeroDivisors C) L) ↔ z ∈ C := by
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have hrange (z : K) : z ∈ (algebraMap 𝒪[K] K).range ↔ z ∈ 𝒪[K] :=
    ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [← hmem x, ← hdual, FractionalIdeal.mem_dual one_ne_zero]
  simp only [Algebra.traceForm_apply, hmem, hrange]

end

theorem field_version (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] (hr : finrank K L = 2)
    (O : Subring L) (hO : ∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x)
    (hU : ∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)})
    (x : L) : (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  have hOC : ∀ z : L, z ∈ O ↔ z ∈ integralClosure 𝒪[K] L := fun z => (hO z).trans Iff.rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm : 𝓂[K] = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hcoe : ∀ c : integralClosure 𝒪[K] L,
      ((c * algebraMap 𝒪[K] (integralClosure 𝒪[K] L) ϖ : integralClosure 𝒪[K] L) : L) =
        (c : L) * algebraMap K L (ϖ : K) := by
    intro c
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[K] K L]
    rfl
  have hmem : ∀ z : integralClosure 𝒪[K] L,
      z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] ↔
        (z : L) ∈ Submodule.span O {algebraMap K L (ϖ : K)} := by
    intro z
    rw [hm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨c, (hOC c).2 c.2⟩, ?_⟩
      rw [← hc, hcoe]
      rfl
    · rintro ⟨a, ha⟩
      refine ⟨⟨a, (hOC a).1 a.2⟩, Subtype.ext ?_⟩
      rw [hcoe, ← ha]
      rfl
  have hU' : ∀ z : integralClosure 𝒪[K] L,
      z * z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] →
        z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] := by
    intro z hz
    rw [hmem] at hz ⊢
    exact hU ϖ hϖ z ((hOC z).2 z.2) hz
  have key := integralClosure_selfDual K L hU' x
  simpa only [hOC] using key

theorem quadraticSelfDual : PI.LocDualGen.W.EpSelfDual := by
  intro K _ _ _ L _ _ hK hC _ hr hred O hO hU x
  haveI := hK
  haveI := hC
  rcases PI.LocDualGen.EpC.dichotomy hr hred with hF | ⟨e, he, h0, h1⟩
  · letI : Field L := hF.toField
    exact field_version K L hr O hO hU x
  · have key := PI.LocDualGen.EpS.selfDual_split hr e he h0 h1 x
    simpa only [hO] using key

end PI.LocDualGen.EpG
