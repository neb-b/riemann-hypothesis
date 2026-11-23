module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem wtc : GlobalTheory.Published.WeilThetaConvergence := GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Rg.Sw.Glob
