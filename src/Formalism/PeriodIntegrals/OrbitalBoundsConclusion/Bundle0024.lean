module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle0001
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0007
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.RenameInitMinor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.QnTInvOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd
section
theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
section
theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl
section
theorem minor_span_complement : PI.MinorSpanCompl := PI.MSC.minorSpanCompl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
section
theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft
end

