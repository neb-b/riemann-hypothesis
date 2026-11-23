module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

namespace ReciprocityTheory.CA.Pt

open IsLocalRing

theorem completionDVR (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    (∃ _ : IsDomain (AdicCompletion (maximalIdeal W) W),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal W) W)) ∧
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal W) W)) (AdicCompletion (maximalIdeal W) W) ∧
    Function.Injective (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    maximalIdeal (AdicCompletion (maximalIdeal W) W) =
      (maximalIdeal W).map (algebraMap W (AdicCompletion (maximalIdeal W) W)) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W, inferInstance,
    AdicCompletion.maximalIdeal_eq_map⟩

end ReciprocityTheory.CA.Pt
