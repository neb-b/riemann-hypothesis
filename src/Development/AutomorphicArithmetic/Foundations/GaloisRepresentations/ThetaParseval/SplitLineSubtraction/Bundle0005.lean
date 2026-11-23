module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClSub
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright
public import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
section
namespace UpperTheory.Gal.TP.Sub

theorem pstOfDR : PstOfDR := pstOfDR_holds GlobalTheory.deRham_potentiallySemistable

theorem frobSub : FrobSub := frobSub_holds cpFacts_holds

theorem clConj : ClConj := clConj_holds cpFacts_holds contLeft_holds pstOfDR

theorem clSub : ClSub := clSub_holds frobSub sumDR_holds pstOfDR wDFacts_holds

theorem clTw : ClTw := clTw_holds frobSub twLoc_holds twJumps_holds pstOfDR wDFacts_holds contLeft_holds

theorem peelAll : PeelAll :=
  peelAll_holds (peelOne_holds dgFacts_holds cpFacts_holds eigTransfer_holds eigSum_holds splitLine_holds sSLeft_holds)
    contLeft_holds clConj clSub

theorem charEx : CharEx :=
  charEx_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter charFrob_holds
    (charAbove_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter HodgeLocalDeRhamField.HLdR.field_outright
      (UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds HodgeLocalDeRhamField.HLdR.field_outright GlobalTheory.deRham_potentiallySemistable) pstOfDR
      contLeft_holds) charInj_holds

end UpperTheory.Gal.TP.Sub
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpMain
section
namespace UpperTheory.Gal.TP.Sub

theorem upOf : UpOf := upOf_holds embSplit_holds wtId_holds satId_holds UpperTheory.Gal.TP.Loc.liftSatU_holds

theorem baseNG : BaseNG := baseNG_holds UpperTheory.Gal.TP.Skew.skewLine_holds

end UpperTheory.Gal.TP.Sub
end

