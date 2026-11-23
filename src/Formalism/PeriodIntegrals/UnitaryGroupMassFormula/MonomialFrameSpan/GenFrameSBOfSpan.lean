module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0002

@[expose] public section

namespace GenFrameSpan

theorem stepSat : StepSat := stepSat_of projZ

theorem genFrameSB_of_span (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat

end GenFrameSpan
