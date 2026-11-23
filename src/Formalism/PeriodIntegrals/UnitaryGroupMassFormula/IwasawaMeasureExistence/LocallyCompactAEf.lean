module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0003

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.MFI

open MeasureTheory Measure NumberField
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

section

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf

theorem locallyCompact_AEf : LocallyCompactSpace (AEf I) :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact_IntAf I)
    ((isOpen_IntAf I).mem_nhds (zero_mem _))

attribute [local instance] locallyCompact_AEf

end

end PI.IwaMeasEx.MFI

end
