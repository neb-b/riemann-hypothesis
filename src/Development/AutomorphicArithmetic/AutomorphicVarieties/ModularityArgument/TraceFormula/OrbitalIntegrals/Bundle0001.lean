module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
section
namespace UpperTheory.V.Z.Tf.Orb

theorem twCentImg_holds : TwCentImg := twCentImg centComm_of

theorem quotAlong_holds : QuotAlong := quotAlong haarComm_of quotIndep_of

theorem inclClosed_holds : InclClosed := inclClosed extCont_of

theorem geoOfMatch_holds : GeoOfMatch := geoOfMatch gLTop_of extCont_of centComm_of twCentImg_holds quotAlong_holds inclClosed_holds

theorem quotReal_holds : QuotReal := quotReal

theorem unitSB_holds : UnitSB := unitSB

theorem unitMatch_holds : UnitMatch := unitMatch gLTop_of extCont_of centComm_of twCent_of haarComm_of quotReal_holds unitSB_holds

theorem geoTransport_holds : GeoTransport := geoTransport

theorem alongIndep_holds : AlongIndep := alongIndep

theorem placeData_holds : PlaceData := placeData

theorem placeOfLocal_holds : PlaceOfLocal := placeOfLocal gLTop_of extCont_of centComm_of haarComm_of twCentImg_holds geoOfMatch_holds geoTransport_holds alongIndep_holds

theorem placeUniq_holds : PlaceUniq := placeUniq

theorem placeInt_holds : PlaceInt := placeInt

theorem placeUnit_holds : PlaceUnit := placeUnit unitMatch_holds unitSB_holds placeData_holds placeOfLocal_holds placeInt_holds

end UpperTheory.V.Z.Tf.Orb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
section
namespace UpperTheory.V.Z.Tf.Orb

theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

theorem gLTop_holds : GLTop := gLTop_of

theorem extCont_holds : ExtCont := extCont_of

theorem centComm_holds : CentComm := centComm_of

theorem twCent_holds : TwCent := twCent_of

theorem haarComm_holds : HaarComm := haarComm_of

theorem quotIndep_holds : QuotIndep := quotIndep_of

theorem normEx_holds : NormEx := normEx_of

theorem quotInt_holds : QuotInt := quotInt_of

theorem untwist_holds : Untwist := untwist_of

theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
end

