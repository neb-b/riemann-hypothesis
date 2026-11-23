module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.FnCrofton

theorem measurable_matrix_gaussian (m n : ℕ) :
    Measurable (matGauss : (Fin m → Fin n → ℂ) → ℝ≥0∞) := by
  unfold matGauss
  fun_prop

theorem measurable_cntOver_first {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S) :
    Measurable fun π : Fin (e + 1) → Fin n → ℂ => cntOver S π (firstCoordVec (e + 1)) := by
  have H := _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver n (e + 1) S hS
  have H2 := H.comp (measurable_id.prodMk (measurable_const (a := firstCoordVec (e + 1))))
  exact H2

theorem encard_fibrePts_inter {n e : ℕ} (S A : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    (((fibrePts S π ∩ A).encard : ℕ∞) : ℝ≥0∞) = cntOver (S ∩ A) π (firstCoordVec (e + 1)) := by
  unfold cntOver
  congr 2
  ext y
  simp only [fibrePts, ptsOver, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

end ModelDimension.FnCrofton
