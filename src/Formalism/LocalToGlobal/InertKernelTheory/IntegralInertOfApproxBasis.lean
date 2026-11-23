module

public import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApprox
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMIsom
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMConj
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BlockFourfoldHOneEqHOne
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0005

@[expose] public section

namespace Formalism.L2.KerInert

theorem isomONB_ofLB (hLB : LocBasisMM) : IsomONB :=
  isomONB_of_facts conjugation_extension_inert hLB rational_coordinates conjugation_fixed_closure


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_approx_basis (hWA : WAPlaces) (hLB : LocBasisMM) : IntInert :=
  integral_inert_of_weakApprox ⟨hWA, one_theta_orthonormal, isomONB_ofLB hLB⟩

end Formalism.L2.KerInert
