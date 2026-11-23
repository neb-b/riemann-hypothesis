module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn

@[expose] public section

namespace MassDataIdxSteps

theorem locOpen_holds : LocOpen := fun X hb _hK _ _ u _ _ p =>
  ⟨stK_holds X p, stRed_of_embP X p (embP_holds X p), stImA_of X hb p (reduction_image_every_place X hb p),
    stImB_of_adaptQ X u p (stAdaptQ_holds X hb u p)⟩

end MassDataIdxSteps
