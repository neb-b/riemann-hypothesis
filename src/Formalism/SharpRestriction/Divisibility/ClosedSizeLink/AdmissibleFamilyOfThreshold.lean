module

public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

section Ev

variable {eps : ℝ} (Fm : FamP eps)

def Ev (P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, P x hx i

variable {Fm}

end Ev

theorem closed_Csz_ge (𝒞 : FamClass) (c : ℝ) : Closed 𝒞 fun Fm _ => c ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

theorem closed_Csz_ge_fn (𝒞 : FamClass) (c : List ℝ → ℝ) : Closed 𝒞 fun Fm _ => c Fm.cOut ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

end Formalism.MainNotions.DIV

end
