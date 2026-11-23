module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjP
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem linOf_one_symm_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by
  rw [LinearEquiv.symm_apply_eq, linOf_one_apply]

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
section
namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem uJClassMass_of_open (s1 : LatStep) (s4 : SurjStep) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep' PI.UnitaryGroupMassFormula.UJClassFin.rational_points_dense s1 s4

end PI.UnitaryGroupMassFormula.UJClassMass
end

