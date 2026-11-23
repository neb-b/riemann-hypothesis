module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi
section
theorem chi_n_bilinear {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Formalism.L2.SG.NormCut.ChiNBi X :=
  PIW.NormChiNBi.chiNBi_holds X
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
section
theorem scalar_equiv_general : PI.ScalPairs.ScalarEquivG :=
  PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds
end

