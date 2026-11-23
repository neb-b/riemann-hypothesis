module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel
section
namespace GlobalTheory.CompanionTheory.CommAlg.SegreFlag

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem segreFlagClosureCut : SegreFlagClosureCut.Statement :=
  SegreFlagClosureCut.proof _root_.GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main
    (PairNumberExpansionIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute)
    NumbersDVR_SegreFlagClosureModel
    (SegreFlagCutSection.proof NumbersDVR_SegreFlagClosureModel
      SegreFlagCutForms.proof SegreFlagCutDivisor.closed segre_flag_degree_zero_holds)
    (SegreFlagCutContraction.proof NumbersDVR_SegreFlagClosureModel
      (SegreFlagCutProjection.proof SegreFlagCutLiesOver.closed NumbersDVR_SegreFlagProjSpecialDim))

end GlobalTheory.CompanionTheory.CommAlg.SegreFlag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

def ptsOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | y ∈ S ∧ linProj π y = w}

def cntOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℝ≥0∞ :=
  (((ptsOver S π w).encard : ℕ∞) : ℝ≥0∞)

def IsScaleStable (S : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ y ∈ S, ∀ t : ℂ, t ≠ 0 → t • y ∈ S

def gaussM (m n : ℕ) : Measure (Fin m → Fin n → ℂ) :=
  (volume : Measure (Fin m → Fin n → ℂ)).withDensity matGauss

def planeMass (n e : ℕ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}

def fibrePts {e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  ptsOver S π (firstCoordVec (e + 1))

def fsSum {e : ℕ} (h : HermNorm n) (u : Fin n → ℂ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (π : Fin (e + 1) → Fin n → ℂ) : ℝ :=
  ∑ᶠ y ∈ fibrePts S π, fsLog h u (h.pointOf y)

def coefRows {e : ℕ} (h : HermNorm n) (π : Fin (e + 1) → Fin n → ℂ) : Fin e × Fin n → ℂ :=
  fun ij => ((h.mat)⁻¹ *ᵥ π ij.1.succ) ij.2


open Classical in
def logGap (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : ℝ≥0∞ :=
  if y = 0 then 0
  else if ∑ j, u j * h.pointOf y j = 0 then ⊤
  else ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y))

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

