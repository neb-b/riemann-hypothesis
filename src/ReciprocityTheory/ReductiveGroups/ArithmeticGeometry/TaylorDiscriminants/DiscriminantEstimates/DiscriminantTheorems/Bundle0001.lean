module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenVan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.PerpendicularDeterminants.PerpVecOfPerp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.UniformDiscreteness.FgOfUnifDiscrete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.IdempotentEvaluation.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.DivPowInteg
section
theorem divided_power_integrality : PI.DivPowInteg :=
  PI.DivPowInteg.Top.divPowInteg_of PI.DivPowInteg.Gen.powXL_holds PI.DivPowInteg.Gen.powXR_holds
    PI.DivPowInteg.Gen.vanL_holds PI.DivPowInteg.Gen.vanR_holds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.FormPartialDerivatives
section
theorem perpendicular_vector_exists : ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt
  intro R _ V _ _ p h e e' g c
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp R V p h e e' g c

theorem perpendicular_vector_perp : ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt
  intro R _ V _ _ p h e e' g hg
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp R V p h e e' g hg
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality
section
theorem schwarz_ball_bound : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := PI.UnitaryGroupMassFormula.TBNum.schwarzBall
theorem euclidean_basis_exists : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := PI.UnitaryGroupMassFormula.TBNum.eBasis
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc
section
theorem discriminant_of_product_lower : ReciprocityTheory.ChartRestriction.G.TB.DiscOfProdLowerSt :=
  PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower

theorem formalGroup_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.FGOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen
section
theorem idempotent_evaluation : ReciprocityTheory.ChartRestriction.G.TB.IdemEvalSt := PI.UnitaryGroupMassFormula.TBIdemDen.idemEval
theorem dual_difference : ReciprocityTheory.ChartRestriction.G.TB.DualDiffSt := PI.UnitaryGroupMassFormula.TBIdemDen.dualDiff
end

