module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def ConeTangentDim.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∀ᵐ y ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)),
        finrank ℂ (coneTangent h J y) = m

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) (y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => y (e.symm (Sum.inl i))

theorem graphBase_graphPt {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) (x : EuclideanSpace ℂ (Fin d)) :
    graphBase e (graphPt e F x) = x := by
  ext i
  simp [graphBase, graphPt]

theorem graphPt_injective_of_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) : Function.Injective (graphPt e F) :=
  Function.LeftInverse.injective (graphBase_graphPt e F)

theorem continuousOn_graphPt {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)} {Ω : Set (EuclideanSpace ℂ (Fin d))}
    (hF : ContinuousOn F Ω) : ContinuousOn (graphPt e F) Ω := by
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
  rcases e j with i | i
  · exact ((PiLp.continuous_apply 2 _ i)).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF

def GraphAreaFibre.Statement : Prop :=
  ∀ (d k n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin k) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)),
    IsOpen Ω → DifferentiableOn ℂ Φ Ω →
    ∀ P ⊆ graphPt e Φ '' Ω, MeasurableSet P →
    ∀ T : EuclideanSpace ℂ (Fin n) → Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ x ∈ Ω, graphPt e Φ x ∈ P → T (graphPt e Φ x) =
        LinearMap.range (fderiv ℂ (graphPt e Φ) x :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) →
    ∀ π : Fin d → Fin n → ℂ,
      AEMeasurable (fun w : EuclideanSpace ℂ (Fin d) =>
          (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) ∧
        ∀ g : EuclideanSpace ℂ (Fin d) → ℝ≥0∞, Measurable g →
          volume (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
                ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
            Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ w : EuclideanSpace ℂ (Fin d),
                (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadBlockGaussTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def LeadBlockGaussTail.Statement : Prop :=
  ∀ (m k : ℕ), 0 < m → ∃ C : ℝ, ∀ r : ℝ,
    ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentGaussInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def TangentGaussInvariant.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n → ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)), finrank ℂ T = m →
    ∀ y ∈ T,
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (tangentJac π T) =
        tangentGaussProfile n m ‖y‖

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def TangentJacComp.Statement : Prop :=
  ∀ (d n : ℕ) (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin d → Fin n → ℂ),
    tangentJac π (LinearMap.range L) * areaJacobian (L.restrictScalars ℝ) =
      |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)|

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacCompress
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

def TangentJacCompress.Statement : Prop :=
  ∀ (n m : ℕ) (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ((tangentJac π T : ℝ) : ℂ) =
      (T.starProjection ∘L (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L
          LinearMap.toContinuousLinearMap (linProjₗ π) ∘L T.starProjection +
        (1 - T.starProjection)).det

end

end GroundTheory.Heights₂.Heights
end

