module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneSmulApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0105
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0101
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0097
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0107
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0104
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0088
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0110
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0106
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0102
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0098
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_deep {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hsig : (VS D).SigOK) (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hst : ProdEP2Cut.StepsU M δ u u' F0 what₂)
    (hSA : TupGlob.StabApprox ⟨δ, M, hA⟩ u u')
    (hFS : FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂) :
    CutAt M δ L u u' F0 what₂ := by
  have hRA : FibPart.RepAtTup M δ u u' F0 what₂ := TupFinal.repAtTup_of_stab ⟨δ, M, hA⟩ u u' F0 what₂ hSA
  have hTF := FibQ.tupFun_holds M δ u u' F0 what₂
  have hOZ := TupOrb.orbZT_holds M δ u u' F0 what₂
  have hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤ :=
    fun Λ hΛ Z => ZsVolFin.finR D u u' F0 what₂ hrows Z Λ hΛ
  have hN : PairVal.NormRepExists D u u' F0 what₂ := PCount.normRepExists_ctx ⟨hc, hrows, hP⟩
  have hM : Formalism.L2.SG.Pf.NormRepMove D u u' :=
    norm_representative_move D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') (Formalism.L2.SG.Closed.TermEqIff_holds D u u')
      (Formalism.L2.SG.Closed.TermFun_holds D u u') hP hsig
  exact cutAt_of_leaves hA hc hP hrows hN hM (local_phase_typed_places hA) (ZsVolAsm.volIdxProd_of_prodE M δ u u' F0 what₂ hP
      (ProdE.prodE_CZ_of_approxC M δ u u' F0 what₂ (ProdEApprox.approxC M δ u u' F0 what₂) hst))
    (fun _ => PCountEx.exist_holds hA u u')
    (fun _ => FibPart.sumFr_of M δ hTF hRA hOZ hA hc hP hN hrows hfin)
    (fun _ => FrameGlobalPatching.frGlob_of_fstar hFS) (PCount.intGenP_holds ⟨δ, M, hA⟩) PCount.tau_one_holds
    (PCount.partnerCount_holds_all ⟨δ, M, hA⟩)
    (FibPart.fibSum_of M δ hTF hRA hOZ) (densTh_of_ga (SplitCoefficientComponents.GaPlusTh_holds M δ u u'))

def CutLeavesDeep (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (_L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ProdEP2Cut.StepsU M δ u u' F0 what₂ ∧
      TupGlob.StabApprox ⟨δ, M, hA⟩ u u' ∧
      FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂

theorem rowsDatumP_of_deep {D : Formalism.BasicNotions.D7} (h : CutLeavesDeep D) : RowsDatumP D := by
  unfold CutLeavesDeep at h
  unfold RowsDatumP
  intro hsig δ M hA L u u' hc hP F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨hst, hSA, hFS⟩ := h hsig δ M hA L u u' hc hP F0 what₂ hrows
  exact rowsDatum_at (cutAt_of_deep (L := L) hsig hA hc hP hrows hst hSA hFS)
    (eligFinite_of (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') hsig hrows) hrows ϖ hϖ nc hnc

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqHolds
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_holds : NormExpDegC :=
  normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds

end Formalism.L2.SG.Pf
end
end

