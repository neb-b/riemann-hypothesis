module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.Bundle0005
public import Mathlib
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.Imports
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairRestrictionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  first | exact @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact fun _ => @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m trivial
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegralStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_theta_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  first | exact @GlobalTheory.MixXUnip.unip_trivial_m | exact fun _ => @GlobalTheory.MixXUnip.unip_trivial_m | exact GlobalTheory.MixXUnip.unip_trivial_m | exact @GlobalTheory.MixXUnip.unip_trivial_m trivial
end

