module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.NotSquareOfJacobiNegOne
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMScale
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModelS
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding

@[expose] public section

namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyTh1S_of_isom (hI : IsomONB) : OneCopyTh1S :=
  oneCopyTh1S_of scale_lattice_bound hI scale_integrality

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyLoc_of_isom (hI : IsomONB) (hz : AlgZero) : OneCopyLoc :=
  oneCopyLoc_ofS lattice_extension (oneCopyTh1S_of_isom hI) (coordTie_of_algZero hz) MModelS.model_series_algebraic change_of_parameters_const_scale

end Formalism.L2.KerInert
