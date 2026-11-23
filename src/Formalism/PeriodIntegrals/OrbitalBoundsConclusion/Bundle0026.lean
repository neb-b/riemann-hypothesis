module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryBothForms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightFixedVectors.HwFixedExMain
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightFixedLine.HwFixedLineMain
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalDataSatisfyLinearHypotheses
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStepOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AAInvTrans
section
theorem operators_commute_translations : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations :=
  AAInvW.operators_commute_translations_of_left_right AAInvW.left_aa
    (AAInvW.rightAA_of AAInvW.operator_model AAInvW.algebra_aa AAInvW.algebra_aa_vector AAInvW.hpk_involution
      AAInvW.subset_upper_hessenberg AAInvW.subset_inverse_column AAInvW.subset_row_star)
    AAInvW.subset_upper_hessenberg
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
section
open Matrix

noncomputable section

namespace PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem ell_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z g = ∑ a : Fin r, flagMat k r z g a.castSucc a.succ := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold flagMat fvec
  rw [dite_eq_left (show (Fin.castSucc a).val < r by simp)]
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left (show (Fin.succ a).val < r by simpa using h), bvec, Matrix.mulVec_single_one,
      Matrix.col_apply]
    rfl
  · rw [dite_eq_right h, dite_eq_right (show ¬ (Fin.succ a).val < r by simpa using h)]
    rfl

end PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRelAtPt in
theorem amplifier_relation_at_point : PI.AmpRoot.RelAtPt := by
  intro k r L p g₀ hc hP hG a ha
  have key := sum_super (ptσ_invol p) (zhat_pt hP.2) (ptζ_ne p) (pt_adj p)
    (flagMat_upper ha.1) (flagMat_diag ha.1) (flagMat_upper ha.2) (flagMat_diag ha.2)
    (flag_rel L.hz.1 L.hz'.1 hP.1 ha)
  have hre : ∀ X : ℂ, (L.c * star X).re = (L.c * X).re := by
    intro X
    calc (L.c * star X).re = (star L.c * star X).re := by rw [hc]
      _ = (star (L.c * X)).re := by rw [star_mul']
      _ = (L.c * X).re := by rw [Complex.star_def, Complex.conj_re]
  unfold psi
  rw [ell_eq L.z a, ell_eq L.z' (g₀⁻¹ * a * g₀), key, hre]
end
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CutoffPlainAndSmoothed
section
theorem cutoff_plain_and_smoothed : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := PI.UnitaryCorollaryDerivatives.unitary_corollary_both_forms
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
section
theorem highest_weight_fixed_exists : PI.HwFix.HwFixedEx := PI.HwFix.UnitaryGroupMassFormula.hwFixedEx_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixLine
section
theorem highest_weight_fixed_line : PI.HwFix.HwFixedLine := PI.HwFix.Line.hwFixedLine_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScXuExists
section
theorem sc_xu_exists : PI.ScXuExists.Target :=
  PI.UnitaryGroupMassFormula.ScXuExists.scXuExists_of PI.UnitaryGroupMassFormula.ScXuExists.local_splitting_projection
    PI.UnitaryGroupMassFormula.ScXuExists.BrA.local_data_satisfy_linear_hypotheses PI.UnitaryGroupMassFormula.ScXuExists.BrB.split_unitary_projection_compatibility
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen
section
theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabPairs
section
theorem stabPairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  PI.StabPairsW.stabPairs_of_converse (PI.StabPairs.Conv.converseStep_of PI.StabPairsW.gram_matrix_invariance)
end

