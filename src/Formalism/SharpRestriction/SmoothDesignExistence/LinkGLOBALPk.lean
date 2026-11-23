module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0004
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem closed_CH (𝒞 : FamClass) : Closed 𝒞 fun _ CH => 0 < CH := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  have h : (1 : ℝ) ≤ CH := hL.2.2.1 CH (by simp [Formalism.MainNotions.FamP.cMid])
  linarith

end Formalism.MainNotions.Pk

end
