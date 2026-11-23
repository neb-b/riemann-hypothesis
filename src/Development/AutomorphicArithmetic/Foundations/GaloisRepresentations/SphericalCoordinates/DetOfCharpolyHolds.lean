module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseImm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBallChar

@[expose] public section

namespace UpperTheory.Gal.W2

theorem TanDeriv_holds : TanDeriv := tanDeriv_of

theorem FlatAffine_holds : FlatAffine := flatAffine_of

theorem ConjCharpoly_holds : ConjCharpoly := conjCharpoly_of

theorem TanChart_holds : TanChart := tanChart_of TanDeriv_holds FlatAffine_holds ConjCharpoly_holds

theorem TanExists_holds : TanExists := tanExists_of

theorem FlatComp_holds : FlatComp := flatComp_of

theorem FlatPre_holds : FlatPre := flatPre_of

theorem PbFlat_holds : PbFlat := pbFlat_of FlatAffine_holds

theorem ExpImm0_holds : ExpImm0 := expImm0_of

theorem ExpImm_holds : ExpImm := expImm_of FlatComp_holds FlatPre_holds PbFlat_holds ExpImm0_holds

theorem HolPi_holds : HolPi := holPi_of

theorem PerNear_holds : PerNear := perNear_of

theorem PerCoordLoc_holds : PerCoordLoc := perCoordLoc_of

theorem PerLin_holds : PerLin := perLin_of

theorem AdExists_holds : AdExists := adExists_of

theorem BaseImm_holds : BaseImm := baseImm_of PerNear_holds PerCoordLoc_holds

theorem PtFibre_holds : PtFibre := ptFibre_of

theorem PtHol_holds : PtHol := ptHol_of HolPi_holds PtFibre_holds

theorem PtImm_holds : PtImm := ptImm_of FlatComp_holds FlatPre_holds PtFibre_holds ExpImm_holds

theorem TriCharpoly_holds : TriCharpoly := triCharpoly_of

theorem DetOfCharpoly_holds : DetOfCharpoly := detOfCharpoly_of

theorem CorrChart_holds : CorrChart := corrChart_of AdExists_holds PerLin_holds PtFibre_holds

theorem LocTan_holds : LocTan := locTan_of TanChart_holds PerNear_holds BaseImm_holds PtHol_holds PtImm_holds PtFibre_holds CorrChart_holds TriCharpoly_holds

theorem DetReal_holds : DetReal := detReal_of

theorem TorusCount_holds : TorusCount := torusCount_of DetReal_holds

theorem PiLattice_holds : PiLattice := piLattice_of

theorem LocSum_holds : LocSum := locSum_of LocTan_holds TorusCount_holds PiLattice_holds PtFibre_holds CorrChart_holds DetOfCharpoly_holds

theorem SimDiag_holds : SimDiag := simDiag_of

theorem ExtendEmb_holds : ExtendEmb := extendEmb_of

theorem KillsMat_holds : KillsMat := killsMat_of

theorem HSep_holds : HSep := hSep_of

theorem DiagExists_holds : DiagExists := diagExists_of SimDiag_holds ExtendEmb_holds KillsMat_holds HSep_holds

theorem TypeCount_holds : TypeCount := typeCount_of

theorem TraceLat_holds : TraceLat := traceLat_of

theorem TraceDual_holds : TraceDual := traceDual_of

theorem NewtonPoly_holds : NewtonPoly := newtonPoly_of

theorem PowSumRat_holds : PowSumRat := powSumRat_of TraceLat_holds TraceDual_holds

theorem RootsFull_holds : RootsFull := rootsFull_of TypeCount_holds PowSumRat_holds NewtonPoly_holds KillsMat_holds

theorem MarkDiag_holds : MarkDiag := markDiag_of TypeCount_holds

theorem TspDiag_holds : TspDiag := tspDiag_of

theorem BallChar_holds : BallChar := ballChar_of TypeCount_holds TspDiag_holds

theorem CspDim_holds : CspDim := cspDim_of SimDiag_holds ExtendEmb_holds TypeCount_holds MarkDiag_holds BallChar_holds

theorem FibDet_holds : FibDet := fibDet_of

theorem FibW_holds : FibW := fibW_of

theorem EvIntegral_holds : EvIntegral := evIntegral_of

theorem EigTop_holds : EigTop := eigTop_of AdExists_holds DiagExists_holds TypeCount_holds RootsFull_holds MarkDiag_holds BallChar_holds FibDet_holds FibW_holds EvIntegral_holds

theorem RootSumW_holds : RootSumW := rootSumW_of

theorem RootSumWOff_holds : RootSumWOff := rootSumWOff_of

end UpperTheory.Gal.W2
