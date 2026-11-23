module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0069
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0077
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016

@[expose] public section

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := _root_.GlobalTheory.CompanionTheory.Eis.idTube
theorem tubeChain : TubeChain := _root_.GlobalTheory.CompanionTheory.TubeFourier.tubeChain
theorem secLaw : SecLaw := _root_.GlobalTheory.CompanionTheory.RgEisSec.secLaw
theorem htLip : HtLip := _root_.GlobalTheory.CompanionTheory.RgEis.htLip
theorem stage : PiLocalization₂ := _root_.GlobalTheory.CompanionTheory.RgEis.stage
theorem wallLaw_of : SecLaw → WallLaw := _root_.GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := _root_.GlobalTheory.CompanionTheory.RgEisGal.gallery
theorem transfer_of : SecLaw → WallLaw → Transfer := _root_.GlobalTheory.CompanionTheory.RgTransfer.transfer
theorem twist_of : SecLaw → Twist := _root_.GlobalTheory.CompanionTheory.RgEisTwist.twist
theorem scale : Scale := _root_.GlobalTheory.CompanionTheory.RgEisScale.scale
theorem grpTop : GrpTop := _root_.GlobalTheory.CompanionTheory.RgEisTop.grpTop
theorem bdetLaw : BdetLaw := _root_.GlobalTheory.CompanionTheory.RgEis.bdetLaw
theorem extLaw : ExtLaw := _root_.GlobalTheory.CompanionTheory.RgEisExt.extLaw
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := _root_.GlobalTheory.CompanionTheory.RgEisPar.parLaw
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := _root_.GlobalTheory.CompanionTheory.RgEisLevi.leviS
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := _root_.GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := _root_.GlobalTheory.CompanionTheory.Plucker.convGrOf
theorem convU_of : ParLaw → ConvU := _root_.GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := _root_.GlobalTheory.CompanionTheory.RgEisTestSph.testSph
theorem stdGood : StdGood := _root_.GlobalTheory.CompanionTheory.StdGoodAd.stdGood
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := _root_.GlobalTheory.CompanionTheory.RgEis.dictInf
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := _root_.GlobalTheory.CompanionTheory.RgEisCM.cmGood
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := _root_.GlobalTheory.CompanionTheory.CMMirror.cmMir
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := _root_.GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
