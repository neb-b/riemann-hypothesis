module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BaseSignsOfVal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Sg

open GlobalTheory.LvT.WtSign Formalism.MainNotions.product_first_zeroth_parts

theorem baseSigns_of_val (X : Stages) (L : SizeData₂ X.toD7) {C : FC} {cD ch : ℝ} (h : Val C cD ch L) :
    GlobalTheory.LvT.WtSign.BaseSigns X.B := by
  have hS : SignLaw X.toD7.hc (· ∈ tops X.toD7) := by
    refine ⟨uLast_le L, fun τ => ?_⟩
    by_cases hτ : τ ∈ tops X.toD7
    · exact eFirst_ge_of_uLast_le _ (uLast_le L τ hτ)
    · apply eFirst_ge_of_uLast_nonpos
      have hk : 0 < X.toD7.R.k := lt_of_lt_of_le (m_pos X.toD7.R) (by have := X.toD7.R.m_add_three_le_k; omega)
      have h1 := (h.hc.2.1 τ hk (fun h' => hτ ((mem_tops τ).2 h'))).2
      unfold uLast
      rw [h1]
      norm_num
  have e : ∀ τ, τ ∈ tops X.toD7 ↔ τ ∈ X.B.wts.tops := fun τ =>
    (mem_tops (D := assemble X.B X.C X.W X.V X.S X.N X.G) τ).trans (X.B.mem_wts_tops τ).symm
  exact ⟨fun τ hτ => hS.1 τ ((e τ).2 hτ), hS.2⟩

theorem baseSigns_of_bPt : ∀ (K : Ctx) (β : BPt K), GlobalTheory.LvT.WtSign.BaseSigns β.X.B :=
  fun _ β => baseSigns_of_val β.X β.p.L β.val

end GlobalTheory.Fc.Sg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColViewOfBuilt
section
noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colView_of_built {𝒮 : GlobalTheory.Mem.Top.Bl.Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : GlobalTheory.Mem.Top.Bl.Built 𝒮 K w Z c) : ColView w Z c.O.tw c.O.nch :=
  { jets := b.pin.jets
    rowInt := b.what₂.rowInt
    tw_eq := congrArg (fun s => s.2.2.1) b.ker_eq
    tup := ⟨b.n.tp, b.n.xi⟩ }

theorem overCols_built : ∀ 𝒮 : Slots, OverCols (IsBuilt 𝒮) ∧ ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) →
    OverCols (positionOf P) := by
  intro 𝒮
  have key : ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) → OverCols (positionOf P) :=
    fun P hP K X f T c hc =>
      positionOf_mono (fun K B f T w Z c h => let ⟨b⟩ := hP K B f T w Z c h; colView_of_built b) K X f T c hc
  exact ⟨key (BuiltC 𝒮) fun _ _ _ _ _ _ _ h => h, key⟩

end GlobalTheory.Fc.Cv

end
end

