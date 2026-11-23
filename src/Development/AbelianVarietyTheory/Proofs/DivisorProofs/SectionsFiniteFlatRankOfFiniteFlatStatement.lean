module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_finite_flat_rank_of_isFinite_flat : ∀ (X T : Scheme.{0}) (p : X ⟶ T) [IsFinite p] [Flat p] (r : ℕ), (∀ t, p.finrank t = r) → ∀ (U : T.Opens), IsAffineOpen U → letI := (p.app U).hom.toAlgebra; Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(X, p ⁻¹ᵁ U) q = r := by
  intro X T p hfinite hflat r hr U hU
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  have hpb := GlobalTheory.isPullback_fromSpec_app_preimage_of_affine p hU hV
  have hfin : IsFinite (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb hfinite
  have hflat' : Flat (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb hflat
  have h1 : (p.app U).hom.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have h2 : (p.app U).hom.Flat := Flat.SpecMap_iff.1 hflat'
  letI := (p.app U).hom.toAlgebra
  haveI : Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h1
  haveI : Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h2
  refine ⟨inferInstance, inferInstance, fun q ↦ ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb q
  rw [hr] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end
