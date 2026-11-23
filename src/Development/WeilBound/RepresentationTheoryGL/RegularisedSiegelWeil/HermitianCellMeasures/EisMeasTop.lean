module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLeOfMinor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0569
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0619
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisMeas

@[expose] public section

namespace PositivityTheory.Rg.Rsw.Em

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem eisMeas : IdemEx → BumpEx → Major → FixW → FixTh → ThProd → MuCell → FibEx → RCell → PosExt → ApproxId → EisMeas :=
  fun hI hB hM hW hT hP hC hF hR hE hA =>
  have hX := GlobalTheory.CompanionTheory.RswEmTop.topX
  have hRi := GlobalTheory.CompanionTheory.AlgRich.algRich hI hB hX
  have hS := GlobalTheory.CompanionTheory.SigL.main hI hX
  GlobalTheory.CompanionTheory.EisE.eisMeas hI hB hM hW hT hP hC hF hR hX hRi hS
    (GlobalTheory.CompanionTheory.OrbExist.orbEx hI hA (GlobalTheory.CompanionTheory.EisDens.dens_main hE) hX hRi (GlobalTheory.CompanionTheory.AlgStab.algStab hI) hS (GlobalTheory.CompanionTheory.HermSc.hermScale_main hI hX))

end PositivityTheory.Rg.Rsw.Em
