module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffQuotientXSq
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0006

@[expose] public section

namespace Formalism.L2.Th1.B

theorem wAdd : WAdd := SAdd.weierstrass_addition_holds
theorem wPrimeU : WPrimeU := GCob.weierstrass_derivative_unit_holds
theorem gCob : GCob := GCob.GCob_of wAdd wPrimeU
theorem lDiv : LDiv := LDiv.LDiv_of gCob
theorem beESim : BeESim := BeE.BeESim_of gCob lDiv
theorem first_cocycle_simeq_zero : CocycleDiffExpEquiv := BeE.cocycle_diff_exp_equiv
theorem cubeE : CubeE := BeE.CubeE_of beESim first_cocycle_simeq_zero

end Formalism.L2.Th1.B
