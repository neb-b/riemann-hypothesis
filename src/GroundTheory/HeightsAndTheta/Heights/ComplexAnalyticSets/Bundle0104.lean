module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PlaceOnComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ J : Ideal (MvPolynomial (Fin n) ℂ),
        J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧ ringKrullDim (curveLocalRing J q) = 1 ∧
        ∃ P' : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def PrimeBranchDimOne.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimePlaceBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimePlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (curveLocalRing J q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation J q), ∃ ν : VarBranch J 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionUnramifiedGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjectionUnramifiedGeneric.Statement : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (Q : Ideal (MvPolynomial (α ⊕ β) ℂ)) (r : ℕ)
    (q : Fin r → MvPolynomial (α ⊕ β) ℂ) (t : MvPolynomial (α ⊕ β) ℂ), Q.IsPrime →
    (∀ b : β, ∃ F : Polynomial (MvPolynomial α ℂ), F.Monic ∧
      F.eval₂ (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom (X (Sum.inr b)) ∈ Q) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial (α ⊕ β) ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        ∀ v : α ⊕ β → ℂ, (∀ a : α, v (Sum.inl a) = 0) →
          (∀ j, ∑ s, eval w (pderiv s (q j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRadialPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

def RadialPrimitive.Statement : Prop :=
  ∀ (e : ℕ) (a : ℝ → ℝ) (t₀ T : ℝ),
    ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 →
      ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ (∃ R : ℝ, ∀ t, R ≤ t → Q t = 0) ∧
        deriv Q 0 = a 0 ∧ deriv (deriv Q) 0 = 0 ∧
        ∀ t, 0 < t →
          deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - radialTransform (e + 1) a t ∧
            deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * radialTransform (e + 1) a t

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def SameOrdersLiftCentre.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : NormalModel J)
    (γ γ' : VarBranch J 1 q) (Γ Γ' : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) →
    (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) →
    DifferentiableOn ℂ Γ' (Metric.ball 0 γ'.radius) →
    (∀ τ ∈ Metric.ball 0 γ'.radius, Γ' τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ' τ) = γ'.toFun τ) →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder γ f = branchOrder γ' f) →
      Γ 0 = Γ' 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserBranchSimpleZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserBranchSimpleZero.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ)
    (r : ℝ) (φ : (Fin 1 → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) → φ 0 = w →
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 1

end

end GroundTheory.Heights₂.Heights
end

