module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0009

@[expose] public section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open ValuationNonnegativity

namespace FrobP

variable {C : Type} [Field C] {V : VF C}

end FrobP


namespace FrobP

variable {C : Type} [Field C] {V : VF C}

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

end FrobP


end Formalism.L2.FormalSeriesBounds
