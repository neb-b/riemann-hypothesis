module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0013
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnPolynomialCovectorZero

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def GrowthBoundInterfaceConditions : Prop := RestCols ∧ RestPre ∧ RestTCore

theorem extendedClosedForm_of_interfaceConditions {D : Formalism.BasicNotions.D7} (h : admitted D → GrowthBoundInterfaceConditions) : ExtendedClosedForm D := stmtEExt_of_15c fun hA => rest_assumptions_of_three_interfaces hA (h hA).1 (h hA).2.1 (h hA).2.2

theorem growthBoundInterfaceConditions : GrowthBoundInterfaceConditions := ⟨restCols, restPre, restTCore⟩

theorem extendedClosedForm (D : Formalism.BasicNotions.D7) : ExtendedClosedForm D := extendedClosedForm_of_interfaceConditions fun _ => growthBoundInterfaceConditions

end Formalism.MainNotions.ColumnSystems.Pf
