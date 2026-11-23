module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FixedZ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatIntegralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0003

@[expose] public section

noncomputable section

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termsAtFinite_of_frameOp_shortFin (hF : FrameOp) (hS : ShortFin) (D : D7) (u u' : D.what₂.Word) :
    TermsAtFinite D u u' :=
  termsAtFinite_of (zhatReduce_of cellReduce_holds hF carrierRow_holds zhatIntegral_holds)
    (fixedZhat_of heisOp_holds skewSolve_holds hS rowsDep_holds rightInv_holds fInt_holds resFin_holds) D u u'

end PI.TermsAtPtFiniteW
