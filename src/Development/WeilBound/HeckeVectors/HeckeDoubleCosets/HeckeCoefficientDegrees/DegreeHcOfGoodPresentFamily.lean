module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender

@[expose] public section

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.D.Upq.Coef

section UJ

open ReciprocityTheory.ChartRestriction.DS

theorem fdeg_gap (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, hc, hH⟩ := fdCons_muG n ε
  refine ⟨c, hc, fun lam h H _ _ _ σ v hl hσ hgap hh hp hq hv => ?_⟩
  have hn : 1 ≤ n := hp.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have ht : thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
    have hp_le : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq_le : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq0_le : S7.q0 ε ≤ n := (min_le_right _ _).trans hq_le
    have hp_real : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp_le
    have hq_real : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq_le
    have hq0_real : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq0_le
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_le_cube : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn_real (by norm_num)
    have hsq_le_cube : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_right₀ hn_real (by norm_num)
    unfold thrStar
    apply max_le
    · have hprod : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
      nlinarith
    · have hsqrt : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n :=
        Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
      have hprod : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
      nlinarith
  refine hH lam H σ v hl hσ h hgap (by linarith) hp hq (fun μ hμ hg => ?_) hv
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
      le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hg hq0 h8
  exact ⟨T, Ψ, hP⟩

end UJ


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq]

end CompanionTheory.D.Upq.Coef

end
