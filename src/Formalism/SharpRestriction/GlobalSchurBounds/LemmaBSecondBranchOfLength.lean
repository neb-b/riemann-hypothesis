module

public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticeOfRankSlopeLength
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0009

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Classical

def ConcreteFormsLevelZero (D : D7) (u : D.what₂.Word) : Prop := FormsTwistCompatibilityFamily D u ∧ product_first_zeroth_parts.admS D u

def FreeTT (D : D7) (u : D.what₂.Word) : Prop := ConcreteFormsLevelZero D u → Nonempty (product_first_zeroth_parts.FreeT D u)

def SlopeLineT (D : D7) (u : D.what₂.Word) : Prop := product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → product_first_zeroth_parts.SlopeLine D u

def SecondBranchIntegralityUnderForms (D : D7) (u : D.what₂.Word) : Prop :=
  product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength D u

variable {eps : ℝ}

theorem slope_free_branch_family (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u)
    (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u) (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u) :
    FamU Fm (fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) ∧ FamU Fm product_first_zeroth_parts.SlopeLine ∧ FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength := by
  unfold FamU at tT ⊢
  obtain ⟨x0, hx⟩ := tT
  exact ⟨⟨x0, fun x h0 h1 i u hS => hWT _ u (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hμT _ u hS (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hBT _ u hS (hx x h0 h1 i u hS)⟩⟩

end Formalism.MainNotions.RT

end
