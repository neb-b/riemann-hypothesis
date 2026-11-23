module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
public import Development.WeilBound.CoreStatements.ResolutionCharZero.Bundle0003

@[expose] public section

namespace NadelVanishingSeparation.NSI

theorem isolatedNonKltDivisor : GlobalTheory.Published.IsolatedNonKltDivisor :=
  GlobalTheory.isolatedNonKltDivisor_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
