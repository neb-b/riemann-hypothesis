module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0227
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0287
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0118
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0177
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0173
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0179
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0107
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0280
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberBundlesLargeUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0205
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0175
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0283
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftHypothesesOfNonvanishing
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Fc.S0.StageU
theorem hypotheses_nonempty_of_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → S0.RowRat → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)) _root_.GlobalTheory.Fc.S0.FunctionalCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)) _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries → Nonempty (_root_.GlobalTheory.Fc.HypsAlt S0.NL _root_.GlobalTheory.Fc.DefiniteSideCondition) := by
  intro P hR hL cDep A hA hN hF hL3
  obtain ⟨hP, hMem, hEx⟩ := _root_.GlobalTheory.T.large_unramified_exponent_bundles_exist_alt P hR hL cDep A hA
  obtain ⟨_, prN, serN, _⟩ := _root_.GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois P.litN P.toHypothesesX
  have hOL := _root_.GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P
  have hO := _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses P hL cDep
  have hNrow := _root_.UpperTheory.GalC.final_alt_alt P.nLink prN P.toHypothesesX serN P.depthZeroSupport'
    P.localFiniteness P.localTateDuality P.localEulerChar hL cDep hN
  let extension := _root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL
    (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A
  have hmono := _root_.GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL
    (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) extension SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hO' := hmono.2 hO
  have hN' : _root_.GlobalTheory.Fc.RL.LinkedAt
      (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension extension SExt.none (geoCl anyGeometry))
      (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L S0.NL) :=
    hmono.1 (fun 𝒜 _ => S0.NL (Cp.D3 3 𝒜)) hNrow
  have hAll := _root_.GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt P.globalArtinReciprocity P.siegelWeilUnitaryConvergent2 P.discreteSeriesCover
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.discreteSeriesClassification hOL.1 hOL.2
    hL _ _ _ S0.NL hO' hL3 hF hN'
  exact _root_.GlobalTheory.Fc.nonempty_hyps_of_allRows_alt hP GlobalTheory.ThinScaleLiterature.litThin GlobalTheory.wuDecayOfGap GlobalTheory.rowsFinDim_link
    GlobalTheory.rowsPos_typeP (GlobalTheory.rowNGP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.rowMainEqP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2) GlobalTheory.genusMassAt_two
    KPx _ _ _ S0.NL _root_.GlobalTheory.Fc.DefiniteSideCondition (fun _ => hMem) hEx hAll
end GlobalTheory.Fc.S0.StageU
end
end
