module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.QmBorderFullOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin
section
theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeConjNorm
section
theorem conjugate_norm_bound : PI.BeConjNorm.BeConjNorm :=
  PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts
section
theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni
section
theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull
section
theorem quantum_minor_border_full : PI.QmBorderFull :=
  PI.qmBorderFull_of quantum_minor_border_es quantum_minor_column_expansion quantum_minor_row_expansion quantum_minor_skip
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPsiExists
section
theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
end

