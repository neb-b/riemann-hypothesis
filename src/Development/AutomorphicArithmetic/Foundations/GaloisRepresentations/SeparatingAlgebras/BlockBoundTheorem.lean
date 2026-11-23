module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GlobOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CongSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0013
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MaxCpt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

@[expose] public section

namespace UpperTheory.Gal.Gen

theorem hB_holds : HB := hB_pf
theorem detLow_holds : DetLow := detLow_pf
theorem fixVec_holds : FixVec := fixVec_pf
theorem flag_holds : Flag := flag_pf fixVec_holds
theorem triMat_holds : TriMat := triMat_pf flag_holds
theorem groupDet_holds : GroupDet := groupDet_pf triMat_holds detLow_holds
theorem alg_holds : Alg := alg_pf hB_holds groupDet_holds
theorem codim_holds : Codim := codim_pf
theorem hS_holds : HS := hS_pf
theorem rFormula_holds : RFormula := rFormula_pf
theorem rConj_holds : RConj := rConj_pf rFormula_holds
theorem wtPos_holds : WtPos := wtPos_pf
theorem meanVal_holds : MeanVal := meanVal_pf
theorem densCont_holds : DensCont := densCont_pf
theorem halfInt_holds : HalfInt := halfInt_pf wtPos_holds meanVal_holds densCont_holds
theorem nullZero_holds : NullZero := nullZero_pf
theorem injAE_holds : InjAE := injAE_pf nullZero_holds
theorem densSymm_holds : DensSymm := densSymm
theorem rDens_holds : RDens := rDens_pf rFormula_holds densSymm_holds
theorem rInt_holds : RInt := rInt_pf injAE_holds rDens_holds halfInt_holds densCont_holds
theorem starEx_holds : StarEx := starEx_pf
theorem symEx_holds : SymEx := symEx_pf
theorem small_holds : Small := small_pf symEx_holds starEx_holds nullZero_holds densCont_holds
theorem gammaEig_holds : GammaEig := gammaEig_pf
theorem gammaInt_holds : GammaInt := gammaInt_pf rInt_holds densCont_holds
theorem gammaConj_holds : GammaConj := gammaConj_pf rConj_holds
theorem repsEx_holds : RepsEx := repsEx_pf
theorem planch_holds : Planch := planch_pf gammaInt_holds gammaConj_holds gammaEig_holds injAE_holds densCont_holds
theorem combine_holds : Combine := combine_pf
theorem restrict_holds : Restrict := restrict_pf
theorem algC_holds : AlgC := algC_pf alg_holds
theorem locOp_holds : LocOp := locOp_pf repsEx_holds planch_holds
theorem satEx_holds : SatEx := satEx_pf
theorem globOp_holds : GlobOp := globOp_pf locOp_holds
theorem neglAt_holds : NeglAt := neglAt_pf globOp_holds small_holds
theorem congSub_holds : CongSub := congSub_pf
theorem tower_holds : Tower := tower_pf congSub_holds
theorem levFacts_holds : LevFacts := levFacts_pf
theorem locComm_holds : LocComm := locComm_pf
theorem ratFin_holds : RatFin := ratFin_pf
theorem ellGrp_holds : EllGrp := ellGrp_pf
theorem ell_holds : Ell := ell_pf ellGrp_holds
theorem wBound_holds : WBound := wBound_pf
theorem countCore_holds : CountCore := countCore_pf hS_holds wBound_holds
theorem cover_holds : Cover := cover_pf levFacts_holds locComm_holds
theorem sep_holds : Sep := sep_pf levFacts_holds locComm_holds ratFin_holds
theorem partFacts_holds : PartFacts := partFacts_pf
theorem count_holds : Count := count_pf countCore_holds cover_holds sep_holds partFacts_holds
theorem countGen_holds : CountGen := countGen_pf count_holds neglAt_holds
theorem stepCore_holds : StepCore := stepCore_pf algC_holds codim_holds partFacts_holds
theorem smoothAt_holds : SmoothAt := smoothAt_pf
theorem step_holds : Step := step_pf smoothAt_holds tower_holds levFacts_holds ell_holds countGen_holds stepCore_holds partFacts_holds
theorem denseGen_holds : DenseGen := denseGen_pf step_holds partFacts_holds
theorem toPolyX_holds : ToPolyX := toPolyX_pf partFacts_holds
theorem kappa_holds : Kappa := kappa_pf
theorem denomBdd_holds : DenomBdd := denomBdd_pf
theorem degLe_holds : DegLe := degLe_pf
theorem blockBound_holds : BlockBound := blockBound_pf
theorem detBound_holds : DetBound := detBound_pf
theorem sizeLe_holds : SizeLe := sizeLe_pf
theorem rhoBound_holds : RhoBound := rhoBound_pf degLe_holds blockBound_holds detBound_holds sizeLe_holds
theorem latFacts_holds : LatFacts := latFacts_pf
theorem levelEx_holds : LevelEx := levelEx_pf
theorem frameW_holds : FrameW := frameW_pf kappa_holds denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds
theorem maxCpt_holds : MaxCpt := maxCpt_pf
theorem powNhds_holds : PowNhds := powNhds_pf
theorem kerOpen_holds : KerOpen := kerOpen_pf powNhds_holds
theorem charSum_holds : CharSum := charSum_pf
theorem twistPart_holds : TwistPart := twistPart_pf
theorem tyStep_holds : TyStep := tyStep_pf levFacts_holds ell_holds kerOpen_holds charSum_holds twistPart_holds

end UpperTheory.Gal.Gen
