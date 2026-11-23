module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLattice
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoLeaves
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.Imports

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.DarbouxCoordinatesGoodModel
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.darboux_coordinates_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  first | exact @PositivityTheory.Mix.darboux_model_rational_lattice | exact fun _ => @PositivityTheory.Mix.darboux_model_rational_lattice | exact PositivityTheory.Mix.darboux_model_rational_lattice | exact @PositivityTheory.Mix.darboux_model_rational_lattice trivial
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPairConverse
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_pair_converse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact fun _ => @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral trivial
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPlaneLocal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_plane_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction trivial
end

