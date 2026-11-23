module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselLeviAction.MulVecBvecApply
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.CoeffMulCharIdem
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockWeightDegree.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid
section
theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi
section
theorem bessel_levi_formula : PI.BesselLevi.BesselLevi :=
  PI.UnitaryGroupMassFormula.BesselLevi.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
section
theorem orthogonalCentral : PI.CharIdem.CharIdem :=
  PI.CharIdemW.charIdem_of PI.CharIdemW.central PI.CharIdemW.scalar
    (PI.CharIdemW.mulEq_of PI.CharIdemW.scalar)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CoefExt
section
theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DefPosDef
section
theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum
section
theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExistsGaugeNormalizedStabilizer
section
theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpIntW
section
theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpTri
section
theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockHarmSplit
section
theorem harmonicSplitting_holds : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockWtDeg
section
theorem highestWeightDegree_le : PI.FockDegreeTwoParts.WtDeg := PI.FockWtDegWork.wtDeg
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult
section
open PI.FoldMult.UnitaryGroupMassFormula

theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
end

