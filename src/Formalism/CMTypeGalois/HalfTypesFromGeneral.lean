module

public import Formalism.CMTypeGalois.CMTypeFrobenius.Bundle0001
public import Formalism.CMTypeGalois.StatementField
public import Mathlib
public import Formalism.Bundle0002

@[expose] public section

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois

end Formalism.Q3
