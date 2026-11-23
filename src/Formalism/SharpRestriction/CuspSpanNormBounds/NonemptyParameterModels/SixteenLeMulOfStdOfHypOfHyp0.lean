module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S.Inh

section a5

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

theorem tau_index_set_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  first
  | exact D.eTau.nonempty
  | exact ⟨D.eTau.symm 1⟩

variable {eps : ℝ}

end a5

end Formalism.MainNotions.S.Inh
