module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0186
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0179
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0235
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0185
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly

@[expose] public section

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := _root_.GlobalTheory.CompanionTheory.MirSides.sideOf hG hB
    have hZ := _root_.GlobalTheory.CompanionTheory.ZetaAlongK.zetaK hC
    _root_.GlobalTheory.CompanionTheory.EisMir.mirGen_of_core hS hSph _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem (_root_.GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) hO (_root_.GlobalTheory.CompanionTheory.EisTestK.testK hG hB hT)
      (_root_.GlobalTheory.CompanionTheory.EisCore.wall_core hM _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood (_root_.GlobalTheory.CompanionTheory.RgEisMG.master _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood _root_.GlobalTheory.CompanionTheory.RgEisHGood.hGood _root_.GlobalTheory.CompanionTheory.RgEisLeft.bGood) hO _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ
        (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideUnfold hC (_root_.GlobalTheory.CompanionTheory.RgEisUnfold.unfold hS _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ) (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideConv hC hSph _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term) (_root_.GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain hM))

end PositivityTheory.RgEis.MG
