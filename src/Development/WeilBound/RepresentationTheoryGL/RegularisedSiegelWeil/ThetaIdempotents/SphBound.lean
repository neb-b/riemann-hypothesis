module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0649
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0684
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018

@[expose] public section

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := _root_.GlobalTheory.CompanionTheory.JacobiMaps.mapsExist
theorem htExist : HtExist := _root_.GlobalTheory.CompanionTheory.HtEx.htExist
theorem heckeEta : HeckeEta := _root_.GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta
theorem fjEis : FJEis := _root_.GlobalTheory.CompanionTheory.FJE.fjEis _root_.GlobalTheory.CompanionTheory.ZUnf.zUnfold _root_.GlobalTheory.CompanionTheory.ThTw.thTwist
theorem pcBound : PcBound := _root_.GlobalTheory.CompanionTheory.PcB.pcBound
theorem rSec : RSec := _root_.GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist htExist
theorem eisHol : EisHol := _root_.GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist htExist
theorem thTotal : ThTotal := _root_.GlobalTheory.CompanionTheory.ThTot.thTotal heckeEta
theorem cfFJ : CfFJ := GlobalTheory.T.fourier_jacobi_coefficient_of_bound pcBound
theorem pcFc : PcFc := _root_.GlobalTheory.CompanionTheory.PcFc.target mapsExist GlobalTheory.T.fourier_zero_holds
theorem sphBound : SphBound := _root_.GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist htExist
theorem resMu : ResMu :=
  _root_.GlobalTheory.CompanionTheory.ResMu.resMu_main mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds _root_.GlobalTheory.CompanionTheory.SWCoef.coefDataExists
theorem polar : Polar :=
  _root_.GlobalTheory.CompanionTheory.RswPolar.polar mapsExist htExist heckeEta _root_.GlobalTheory.CompanionTheory.Dblock.rightId _root_.GlobalTheory.CompanionTheory.PoleBound.poleReal fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
