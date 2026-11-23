module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0051
public import Formalism.SharpRestriction.LevelLetterCocycles.SplitShapeLRec
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0047
public import Formalism.SharpRestriction.LevelLetterCocycles.ReductionZeroOfPrincipalUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0039
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0035

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrobeniusLevels
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_frobenius (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm := fun hA =>
  arc_coordinates_of_levels D HW F Cm (lev0MpL_of D HW F Cm hA h4 h9) h2 hA

theorem arc_coordinates_of_frobenius_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h2 : LevelZeroModPRefinedLocal D HW) : ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius D HW F Cm h4 h9 h2 hA

theorem split_case_A_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm)
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D)
    (h2 : LevelZeroModPRefinedLocal D HW) : SplittingArcLifting D HW F Cm :=
  splitting_of_literature_exactness D HW F Cm hA h6 hH hTr hWX hFont
    (splitShapeL_rec D HW F Cm hArc (lev0MpL_of D HW F Cm hArc h4 h9) h2 h23 h17)

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralStatementHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem toolsAlg_at (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL h.2.2) := by
  have hR : ToolsR.RingP ((HW l).W K 1 LL h.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O ((HW l).W K 1 LL h.2.2)
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  exact ⟨ToolsR.tools1 hR, ToolsR.tools2 hR hp0 hpu, ToolsR.tools3 hR, ToolsR.tools4 hR⟩

theorem invLevCore_fin (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  refine InvW.invLevCore_L D HW F h9 fun l _ K LL h a s hB => ?_
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  exact InvW.levRat_of ((HW l).W K 1 LL h.2.2) (ring_condition_uniformizer_polynomial D HW F h9 l K LL h) (toolsAlg_at D HW F h9 l K LL h)
    (Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)) a s hB

theorem universal_general_statement_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_level_inverse D HW F Cm hAdm h9 hH h15 (invLevCore_fin D HW F h9)

end Formalism.MainNotions.UnusedSlot80
end
end

