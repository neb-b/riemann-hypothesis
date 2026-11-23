module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSFlagindep
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectation

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof _root_.GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    _root_.GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicatorStatement
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_projection_ball_indicator : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectationStatement
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_set_sum_expectation : ∀ {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
  (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞), Measurable φ →
  (∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞)) →
  (∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) →
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts <;> assumption)
end

