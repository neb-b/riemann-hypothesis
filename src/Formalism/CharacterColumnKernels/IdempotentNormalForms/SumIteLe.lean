module

public import Formalism.CharacterColumnKernels.Bundle0002
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

theorem etaBound : LocalSubalgebraEtaBound := by
  intro O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB
    B hB
  refine (congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG
    haB).trans ?_
  refine sum_le_sum fun x hx => ?_
  gcongr
  exact hB x hx

end Formalism.NG
