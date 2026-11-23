module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0047

@[expose] public section

namespace Formalism.L2.SG.Pf

theorem ooLintSumC_outright : OOLintSumC :=
  ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

theorem absConvC_outright : Formalism.L2.SG.Full.AbsConvC := absConvC_holds_of ooLintSumC_outright

end Formalism.L2.SG.Pf
