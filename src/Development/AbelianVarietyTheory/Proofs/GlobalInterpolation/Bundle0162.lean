module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsView
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMember
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumns
section
noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem overCols_goodE : ∀ (𝒮 : Slots) (R : V4.Slot), OverCols (IsGoodE 𝒮) ∧ OverCols (sAnd (IsGoodE 𝒮) R) := by
  intro 𝒮 R
  have h : OverCols (IsGoodE 𝒮) :=
    (overCols_built 𝒮).2 (GoodE 𝒮) fun _ _ _ _ _ _ _ g => ⟨g.1.choose⟩
  exact ⟨h, OverCols.and_left h⟩

end GlobalTheory.Fc.Cv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumn
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem row_level_valuations : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  refine Row0.row (H := EvC fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u)
    (validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hβ => ?_)) Lk
  refine _root_.GlobalTheory.Fc.Cv.view_at_built (fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u) ?_ K β
    (hQ _ _ _ _ _ hβ)
  intro B f T w Z O nch hv hs _ u
  rw [hv.tw_eq]
  exact GlobalTheory.LvT.Built.TrueCols.closing_true_cols w.I w.ok hv.jets hs w.l Z w.l0 O.X u

end GlobalTheory.Fc.Cv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealSideColumnsCompatibleBundlePointsOverColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

def TiePt (D : D7) (_ : Obj D) : Prop :=
  Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)

theorem row_tie_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.Row_tie Q Lk := by
  intro Q hQ Bd Lk
  have hpt : ∀ (K : Ctx) (β : BPt K), β.Is HasCols → TiePt β.D β.O :=
    _root_.GlobalTheory.Fc.Cv.view_at_built TiePt fun B f T w Z O nch _ _ hR =>
      ⟨hR, _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_chiFin0 w.I w.ok w.pins w.l Z⟩
  have h0 : Row0 Q (EvC TiePt) :=
    validForConstructedPointClasses_eventuallyWorkingClass (Q := Q) (EvP.of_all fun _ K _ β hq => hpt K β (hQ K β.X β.f β.T β.c hq))
  refine Row0.row (Row.imp h0 fun 𝒜 _ _ h => ?_) Lk
  refine Closed.imp h fun Fm _ _ H => ?_
  obtain ⟨x0, hx0⟩ := H
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := by have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx; linarith
  exact hx0 x e0 e1 i

end GlobalTheory.Fc.PeriodEntriesOverColumns
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsA
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem constructedPoint_referenceChainWord_formsMap (Q : V4.Slot) (hQ : OverCols Q) (K : Ctx) (β : BPt K) (hq : β.Is Q) :
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 β.D u :=
  _root_.GlobalTheory.Fc.Cv.view_at_built (fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (fun _ _ _ w Z _ _ _ _ _ => _root_.GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember w.I w.ok w.pins w.l Z)
    K β (hQ _ _ _ _ _ hq)

theorem referenceChainEvaluation_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints Q Lk :=
  fun Q hQ _ Lk => Row0.row (validForConstructedPointClasses_eventuallyWorkingClass (R := fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (EvP.of_all fun _ K _ β hq => constructedPoint_referenceChainWord_formsMap Q hQ K β hq)) Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols :
    ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h : Row0 Q (EvC fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D) :=
    validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hq =>
      _root_.GlobalTheory.Fc.Cv.view_at_built (fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D)
        (fun _ _ _ w Z _ _ hv _ _ => _root_.GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows w.I w.ok w.pins w.l Z hv.rowInt) K β (hQ _ _ _ _ _ hq))
  exact h.row Lk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPointRowAdmissibleTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem twistedPointIntegral_of_TC_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  intro B X I hI l Z l0 u μ _ _
  exact Formalism.MainNotions.DIV.HookProducts.AdmPtTw.lowerTieTwAt_integral
    (_root_.GlobalTheory.PerQ.lowerTieTwAt_to_lib _ _ u μ (_root_.GlobalTheory.PerQ.lowerTieTwAt_all I hI l Z l0 u μ))

end GlobalTheory.PerQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingFamClassCopiesEqFrozen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem copies_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧
    (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧
    ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  refine ⟨fun 𝒜 eps Fm => ⟨(working_classes_frozen.1 𝒜 eps Fm).2, (working_classes_frozen.1 𝒜 eps Fm).1⟩, fun eps Fm h => ?_⟩
  obtain ⟨a, b, c, d, e, f, g⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm h
  refine ⟨a, b, c, d, e, f, ?_⟩
  obtain ⟨x0, hx0⟩ := g
  exact ⟨x0, fun x hx hx1 i => hx0 x hx hx1 i⟩

end GlobalTheory.Fc
end

