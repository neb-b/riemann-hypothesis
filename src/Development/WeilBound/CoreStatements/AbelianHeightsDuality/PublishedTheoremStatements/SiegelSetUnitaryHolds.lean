module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore

@[expose] public section

namespace PositivityTheory.Prw

theorem siegelCore_holds : PositivityTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Prw
