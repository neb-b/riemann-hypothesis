module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0009
public import GroundTheory.LocalFields.IntermediateField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0072
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
public import GroundTheory.LocalFields.Bundle0010
public import GroundTheory.LocalFields.Eisenstein
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.LocalFields.Bundle0007
public import GroundTheory.LocalFields.Bundle0004
public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.Bundle0008

@[expose] public section

-- bundled from GroundTheory.LocalFields.LowerIndexQuotient
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem addVal_prod {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι : Type*}
    (s : Finset ι) (f : ι → R) : addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) :=
  _root_.Bl.general_b_fact'''''''.goal1 s f

section Restrict

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)

theorem restrictNormalHom_restrictScalars [Normal K M] (τ : L ≃ₐ[M] L) :
    AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M]
  exact ⟨τ, rfl⟩

theorem exists_eq_mul_restrictScalars_of_restrictNormalHom_eq [Normal K M] {σ ρ : L ≃ₐ[K] L}
    (h : AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ) :
    ∃ τ : L ≃ₐ[M] L, σ * τ.restrictScalars K = ρ := by
  have hker : σ⁻¹ * ρ ∈ (AlgEquiv.restrictNormalHom M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M] at hker
  obtain ⟨τ, hτ⟩ := hker
  refine ⟨τ, ?_⟩
  rw [← AlgEquiv.restrictScalarsHom_apply, hτ, mul_inv_cancel_left]

end Restrict

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section

variable (M : IntermediateField K L)

variable [IsGalois K L]

theorem ramificationIndex_mul_lowerIndex_restrictNormalHom [Normal K M] (σ : L ≃ₐ[K] L) :
    ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) :=
  by apply _root_.UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom <;> assumption



theorem exists_lowerIndex_mul_eq_min (σ : L ≃ₐ[K] L) :
    ∃ τ₀ : L ≃ₐ[M] L,
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤
        lowerIndex K L (σ * τ₀.restrictScalars K)) ∧
      ∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ₀.restrictScalars K * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L (σ * τ₀.restrictScalars K)) := by
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun τ : L ≃ₐ[M] L ↦ lowerIndex K L (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ hmax τ (Finset.mem_univ _), fun τ ↦ ?_⟩
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  rw [← lowerIndex_restrictScalars (K := K)]
  rcases lt_or_ge (lowerIndex K L (τ.restrictScalars K)) (lowerIndex K L σ₀) with h | h
  · rw [lowerIndex_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    refine le_antisymm ?_ ((min_eq_left h).symm.le.trans (min_le_lowerIndex_mul _ _))
    have hm : (τ₀ * τ).restrictScalars K = τ₀.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ ↦ rfl
    have := hmax (τ₀ * τ) (Finset.mem_univ _)
    rwa [hm, ← mul_assoc] at this

end

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.TameExtension
section
noncomputable section

open Polynomial IntermediateField ValuativeRel

namespace GroundTheory.LocalField

section Definition

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]



end Definition

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem isUnramifiedSubextension_iff' (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsUnramifiedSubextension E ↔ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  by
    letI : IsNonarchimedeanLocalField E :=
      intermediateField_isNonarchimedeanLocalField_of_finiteDimensional E
    exact ⟨fun h ↦ h.ramificationIndex_eq_one, fun h ↦ (isUnramifiedSubextension_iff_exists E).2
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

end Valued

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

end SlopeTestRemainingChoices

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

end Valued

section Structure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]


variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

end Structure

section Union

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

variable [IsSepClosed Ω]

end Union

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]



end Galois

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

end SeparableClosure

end GroundTheory.LocalField
end
end

