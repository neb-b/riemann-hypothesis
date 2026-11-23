module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore

@[expose] public section

namespace GlobalTheory.CompanionTheory.WTC

theorem weilThetaConvergence_of_core (h : PositivityTheory.ThKR.SiegelCore) : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.T.theta_convergence_of_siegel_set (PositivityTheory.ThKR.siegel_of_core h)

end GlobalTheory.CompanionTheory.WTC
