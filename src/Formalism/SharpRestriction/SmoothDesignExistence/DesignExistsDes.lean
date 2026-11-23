module

public import Formalism.SharpRestriction.MuTuOfTuSize
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Pk

abbrev Des (𝒞 : FamClass) (C0 : ℝ) : FamClass :=
  fun Fm => ((𝒞 Fm ∧ DGamSmooth Fm) ∧ TwGood Fm) ∧ (∃ CH : ℝ, ChosenE Fm C0 CH) ∧ TuSize Fm ∧ DGamSize Fm

abbrev WithSm (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ DGamSmooth Fm

end Formalism.MainNotions

end
