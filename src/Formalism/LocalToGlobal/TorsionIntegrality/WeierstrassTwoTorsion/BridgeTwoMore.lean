module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DifferenceLinearCoeff
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.NormLeOneOfMonicTwo
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WeierstrassPPrimeUnit

@[expose] public section

universe u v

namespace Formalism.L2.Th1.A

theorem bridgeTwoMore : BridgeTwoMore := two_curves_relation
theorem flowUniqueZ : FlowUniqueZ.{u} := flow_unique_integral
theorem bridgeCurve3 : BridgeCurve3 := three_curves_relation

end Formalism.L2.Th1.A
