module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptedIndexVectorCompatibility
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsAdaptedIndexHermitian

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedBasisHermitianUnique
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.adapted_basis_hermitian_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d)),
        Function.Injective j →
        (∀ z, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
        ∀ (v : Pl (F := F)) (φ : (Fin n × Fin d → Fv F v) → ℂ), (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v φ →
          ∃ c : ℂ, c ≠ 0 ∧ (fun y => φ (Function.extend j y 0)) = c • M₁.vac v := by
  first | exact @PositivityTheory.Mix.adapted_index_vector_compatibility | exact fun _ => @PositivityTheory.Mix.adapted_index_vector_compatibility | exact PositivityTheory.Mix.adapted_index_vector_compatibility | exact @PositivityTheory.Mix.adapted_index_vector_compatibility trivial
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsAdaptedBasisHermitian
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.exists_adapted_basis_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∃ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d)),
        Function.Injective j ∧
        (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
          co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
        (∀ z, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) := by
  first | exact @PositivityTheory.Mix.exists_adapted_index_hermitian | exact fun _ => @PositivityTheory.Mix.exists_adapted_index_hermitian | exact PositivityTheory.Mix.exists_adapted_index_hermitian | exact @PositivityTheory.Mix.exists_adapted_index_hermitian trivial
end

