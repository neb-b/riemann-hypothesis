module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0002

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

end
