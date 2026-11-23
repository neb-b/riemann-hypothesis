module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ThetaIntegerIsSSubstitution
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.CoboundaryCommutesHomomorphism
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TraceDualExists
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusExtensionOnInclusion

@[expose] public section

namespace Formalism.L2.Th1.D

theorem kernelOfF : KernelOfF := kernel_of_f
theorem sigmaIsom : SigmaIsom := sigma_isometry
theorem fixedIsLimit : FixedIsLimit := fixed_is_limit
theorem transport_first_level : CoboundaryCocycleTransportAlongHom := transport_first_level_holds
theorem transportNorm : TransportNorm := transport_norm_relation
theorem trDualExists : TrDualExists := trace_dual_exists
theorem frobA : FrobA := frobenius_on_ring_a

end Formalism.L2.Th1.D
