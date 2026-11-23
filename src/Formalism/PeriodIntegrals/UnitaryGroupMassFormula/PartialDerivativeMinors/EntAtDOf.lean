module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0002

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem entAtD_of (hX : PExpCoeff) (hB : PBridge) (hC : PLapComm) (hM : PMinorAff) (hS : PSDegMul)
    (hF : PLapForms) : PI.EntAtD.EntAtD :=
  entAtD_of_core (core_of (expand_of hX) (vanish_of hB hC (lapZero_of hM hS hF)))

end PI.EntAtD.W
