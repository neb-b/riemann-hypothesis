module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.IsExpIntegralParallelogramOfNe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KernelSplitting.IsIntegralHalf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DiffLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
section
theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ClassNumImQInt
section
theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubeRelationOfParallelogram
section
theorem cube_relation_of_parallelogram : PI.FglGram.CubeRelationOfParallelogram := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cubeRelationOfParallelogram
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
section
theorem discrNe' : PI.DiscrNe := DiscrNeWork.discrNe_all
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW
section
theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagGramNonneg
section
theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockRaiseLow
section
theorem gradedOscillatorProperty : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
section
theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
section
theorem locFramePrim : PI.LocFramePrim.Statement :=
  PI.LocFramePrimWork.Steps_top PI.LocFramePrimWork.localDifferentPowerSpan PI.LocFramePrimWork.dualFunctionalsExist
    PI.LocFramePrimWork.primitiveOfDualFunctionals
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
section
theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PowBddInt
section
theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
section
theorem sum_log_p_over_p : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
end

