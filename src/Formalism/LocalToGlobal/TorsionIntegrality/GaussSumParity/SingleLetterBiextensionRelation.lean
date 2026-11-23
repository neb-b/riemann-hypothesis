module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

@[expose] public section

namespace Formalism.L2.Th1.D

theorem nrDense : NRDense := NRDense_of sqrtKur

theorem nrcmOfCM4 : Formalism.L2.Th1.CM.CM4 → NRCM := NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense

end Formalism.L2.Th1.D
