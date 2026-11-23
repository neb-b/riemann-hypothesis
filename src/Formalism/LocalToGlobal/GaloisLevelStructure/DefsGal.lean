module

public import Mathlib

@[expose] public section

namespace Formalism.L2.NG

instance isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end Formalism.L2.NG
