module

public import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Bundle0001
public import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Bundle0002
public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.UChase

@[expose] public section

namespace Formalism.LIFT

theorem lift_LagrangeIdeal : LagrangeIdeal := lagrangian_ideal_holds
theorem lift_LagrangeIdealInt : LagrangeIdealInt := lagrangian_ideal_integral_holds
theorem lift_WBTail : WBTail := wBTail_of gammaGradedStep_holds (lagrangeIdealCyc_of lagrangian_ideal_holds)
theorem lift_LemmaU : LemmaU := lemmaU_of (uClaim_of (uGraded_of gammaGradedStep_holds) gammaGradedStep_holds) uChase_proof

end Formalism.LIFT
