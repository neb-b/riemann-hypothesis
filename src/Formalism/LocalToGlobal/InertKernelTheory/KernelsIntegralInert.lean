module

public import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfApproxBasis
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FrLocB

@[expose] public section

namespace Formalism.L2.KerInert


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem kernels_integral_inert : IntInert := integral_inert_of_approx_basis weak_approximation_places local_orthonormal_basis

end Formalism.L2.KerInert
