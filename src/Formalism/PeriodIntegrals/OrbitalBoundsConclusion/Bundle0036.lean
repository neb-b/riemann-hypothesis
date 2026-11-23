module

public import Formalism.PeriodIntegrals.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseDerivativeFiltration.HasseMemHfr
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH
section
theorem hasse_presentation : PI.HassePresH := PI.UnitaryGroupMassFormula.HassePresH.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_function_const (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermFun D u u' :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termFun_of PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u'
end

