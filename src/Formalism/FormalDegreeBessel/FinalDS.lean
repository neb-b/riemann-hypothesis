module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003

@[expose] public section

namespace Formalism.QuantumDeterminants

theorem fdegPos : FdegPos := formal_degree_pos_holds
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
theorem capelliHW : CapelliHW := capelliHighestWeight_holds

end Formalism.QuantumDeterminants
