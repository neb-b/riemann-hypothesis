module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteType
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_finite_over_localization_atPrime_below (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by
  classical
  let p : Ideal P := 𝔫.comap (algebraMap P B)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl
  have hMle : M ≤ 𝔫.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ h
    exact hs (Ideal.mem_comap.mpr h)
  have hM0 : M ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    show algebraMap P B s ∈ 𝔫
    rw [h0]
    exact 𝔫.zero_mem
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM0
  let algCA : Algebra (Localization M) A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) A M 𝔫.primeCompl hMle
  have : IsScalarTower B (Localization M) A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  let 𝔪 : Ideal (Localization M) := (maximalIdeal A).comap (algebraMap (Localization M) A)
  have h𝔪 : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  have hNA : IsLocalization (𝔫.primeCompl.map (algebraMap B (Localization M))) A :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  have hunitB : ∀ b : B, IsUnit (algebraMap B A b) ↔ b ∈ 𝔫.primeCompl := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔫 b
  have hA : IsLocalization.AtPrime A 𝔪 := by
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := A)
      (M := 𝔫.primeCompl.map (algebraMap B (Localization M))) (N := 𝔪.primeCompl) ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ h
      have hu : IsUnit (algebraMap B A b) := (hunitB b).mpr hb
      rw [IsScalarTower.algebraMap_apply B (Localization M) A] at hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) hu
    · rintro ⟨x, hx⟩
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
      have key : algebraMap B A b =
          algebraMap B A s * algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s) := by
        rw [IsScalarTower.algebraMap_apply B (Localization M) A b,
          IsScalarTower.algebraMap_apply B (Localization M) A s, ← map_mul, IsLocalization.mk'_spec']
      refine ⟨algebraMap B (Localization M) s, b, ?_, (IsLocalization.mk'_spec' _ _ _).symm⟩
      have hs : IsUnit (algebraMap B A s) := (hunitB s).mpr (hMle s.2)
      have hx' : IsUnit (algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s)) := by
        by_contra hn
        exact hx (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
      refine (hunitB b).mp ?_
      rw [key]
      exact hs.mul hx'
  have hcomapB : 𝔪.comap (algebraMap B (Localization M)) = 𝔫 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A 𝔫
  refine ⟨p, hp, Localization M, inferInstance, inferInstance, inferInstance, inferInstance, algCA,
    𝔪, h𝔪, ?_, hA, ?_⟩
  · exact localizationAlgebra_injective (S := B) (M := p.primeCompl) (Localization.AtPrime p)
      (Localization M) hinj
  · let Q : Ideal (Localization.AtPrime p) :=
      𝔪.comap (algebraMap (Localization.AtPrime p) (Localization M))
    have hQ : Q.comap (algebraMap P (Localization.AtPrime p)) = p := by
      show (𝔪.comap _).comap _ = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq P B (Localization M), ← Ideal.comap_comap, hcomapB]
    have h1 : Q = p.map (algebraMap P (Localization.AtPrime p)) := by
      have h2 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q
      rw [Ideal.under_def, hQ] at h2
      exact h2.symm
    show Q = _
    rw [h1]
    exact Localization.AtPrime.map_eq_maximalIdeal

theorem exists_conductor_adicCompletion_of_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  intro A _ _ _ _ _ _
  obtain ⟨r, B, _, _, _, _, _, _, 𝔫, _, hinj, hloc⟩ := _root_.GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial A
  obtain ⟨p, _, C, _, _, _, _, _, 𝔪, _, hinjC, hlocC, hcomap⟩ :=
    exists_finite_over_localization_atPrime_below (MvPolynomial (Fin r) ℤ) B A 𝔫 hinj
  have hTreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  obtain ⟨_, _⟩ := _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime p)
  have := _root_.GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion (Localization.AtPrime p)
  obtain ⟨_, _⟩ := _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (R := MvPolynomial (Fin r) ℤ)
      (IsLocalization.injective (M := p.primeCompl) (S := Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  have hTU : Function.Injective (algebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro x y h
    exact AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) h
  obtain ⟨d, hd0, hd⟩ := _root_.GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) C hTU hinjC
  obtain ⟨S', _, e, he⟩ := _root_.GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod (Localization.AtPrime p) C A 𝔪 hcomap
  have key := GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor (AdicCompletion (maximalIdeal A) A) S' _ e _ hd
  have hed : (e (algebraMap (Localization.AtPrime p) _ d)).1 =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A (algebraMap _ C d)) := by
    rw [Algebra.TensorProduct.algebraMap_apply', he]
  refine ⟨algebraMap C A (algebraMap _ C d), ?_, fun c hc => ?_⟩
  · intro h0
    apply hd0
    apply hinjC
    apply IsLocalization.injective (M := 𝔪.primeCompl) (S := A) 𝔪.primeCompl_le_nonZeroDivisors
    rw [h0, map_zero, map_zero]
  · obtain ⟨s, hs⟩ := key c hc
    exact ⟨s, by rw [hs, hed]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlace
section
open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
section
open Polynomial

namespace GlobalTheory

theorem exists_galois_subfield_conj_stable (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ (∀ z ∈ S, z ∈ K) ∧
      Complex.I ∈ K ∧ ∀ z ∈ K, starRingEnd ℂ z ∈ K := by
  classical
  have hI : IsIntegral ℚ Complex.I := by
    refine ⟨X ^ 2 + C 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [Complex.I_sq]
  have hint : ∀ z ∈ insert Complex.I S, IsIntegral ℚ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hI
    · exact (hS z hz).isIntegral
  obtain ⟨p, hp⟩ : ∃ p : ℚ[X], p = ∏ z ∈ insert Complex.I S, minpoly ℚ z := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact Finset.prod_ne_zero_iff.2 fun z hz => minpoly.ne_zero (hint z hz)
  have hroot : ∀ z ∈ insert Complex.I S, z ∈ p.rootSet ℂ := by
    intro z hz
    rw [mem_rootSet]
    refine ⟨hp0, ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (minpoly ℚ) hz
    rw [hp, hq, map_mul, minpoly.aeval, zero_mul]
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have : p.IsSplittingField ℚ K :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
  have hfin : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K p
  have : Normal ℚ K := Normal.of_isSplittingField p
  refine ⟨K, hfin, IsGalois.mk,
    fun z hz => IntermediateField.subset_adjoin ℚ _ (hroot z (Finset.mem_insert_of_mem hz)),
    IntermediateField.subset_adjoin ℚ _ (hroot _ (Finset.mem_insert_self _ _)), ?_⟩
  let φ : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have hsub : φ '' (p.rootSet ℂ) ⊆ p.rootSet ℂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_rootSet] at hw ⊢
    exact ⟨hw.1, by rw [Polynomial.aeval_algHom_apply, hw.2, map_zero]⟩
  have hle : K.map φ ≤ K := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  intro z hz
  exact hle ⟨z, hz, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerR
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TameRootSurj

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem irreducible_X_pow_sub_C {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) {L : ℕ} (hL : 0 < L) {ϖ : 𝓞 E}
    (hmem : ϖ ∈ P.asIdeal) (hnot : ϖ ∉ P.asIdeal ^ 2) :
    Irreducible (X ^ L - C (ϖ : E)) := by
  have hmon : (X ^ L - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hL.ne'
  have hdeg : (X ^ L - C ϖ : (𝓞 E)[X]).natDegree = L := natDegree_X_pow_sub_C _
  have hEis : (X ^ L - C ϖ : (𝓞 E)[X]).IsEisensteinAt P.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using P.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hL.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ L - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible P.isPrime hmon.isPrimitive (by rw [hdeg]; exact hL)
  have hmap : (X ^ L - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ L - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  intro E Ω _ _ _ _ _ P A L ϖ π hA hL h1 h2 hπ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0, eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1 : L = 1 := by omega
    subst hL1
    refine ⟨1, one_mem _, ?_⟩
    rw [AlgEquiv.one_apply, div_self hπ0]
    exact IsPrimitiveRoot.one
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((L : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hL0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  have hirr := irreducible_X_pow_sub_C P (Nat.pos_of_ne_zero hL0) h1 h2
  have hmon : (X ^ L - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hL0
  have hr1 : aeval π (X ^ L - C (ϖ : E)) = 0 := by simp [hπ]
  have hr2 : aeval (ζ * π) (X ^ L - C (ϖ : E)) = 0 := by simp [mul_pow, hζ.pow_eq_one, hπ]
  have hm1 := minpoly.eq_of_irreducible_of_monic hirr hr1 hmon
  have hm2 := minpoly.eq_of_irreducible_of_monic hirr hr2 hmon
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g π = ζ * π := by
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 (hm2.symm.trans hm1)
    exact ⟨g, hg⟩
  obtain ⟨-, hx2⟩ := GlobalTheory.InertiaMovesRoot.cong_on_adjoin hA hL2 h1 h2 hπ
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) π
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := 𝓞 E) H
    (primeBelow (F := E) A) g (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {π}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨π, IntermediateField.mem_adjoin_simple_self E π⟩)))
  refine ⟨k' * g * k, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong hc, ?_⟩
  have e1 : k π = π := hk
  have e2 : k' π = π := hk'
  have e3 : (k' * g * k) π / π = k' ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1, hg, map_mul, e2, mul_div_cancel_right₀ _ hπ0]
  rw [e3]
  exact hζ.map_of_injective k'.injective

end GlobalTheory.TameRootSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem host_cmData : ∀ (R : Ranks) (H : Host R), @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  intro R H
  letI := H.cmStar
  have hcm := H.isCMField_hostE
  have hs : ∀ x : H.E, star x = H.conj x := bridge_star_holds R H
  refine ⟨⟨inferInstance, fun φ a => ?_, fun P hP => ?_⟩, inferInstance, ?_, fun a => ?_⟩
  · rw [hs]
    exact H.conjE_apply _ _
  · have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    have h := H.der.unramEF P hP.isPrime hP0
    obtain ⟨x, hx⟩ := not_forall.1 h
    refine ⟨x, H.conj • x, ?_, fun h' => hx ?_⟩
    · rw [hs]; rfl
    · have := P.neg_mem h'
      rwa [neg_sub] at this
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [hs]
    have h := H.conjE_mem_hostF_iff a
    constructor
    · intro ha
      exact ⟨⟨a, h.2 ha⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact h.1 y.2

end GlobalTheory.Mem
end

