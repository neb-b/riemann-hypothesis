module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique

@[expose] public section

namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique :=
  GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 discreteSeriesUpqUnique

end GlobalTheory.CompanionTheory.Front
