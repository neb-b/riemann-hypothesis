module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopNadel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopIsolated
public import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopPointSep

@[expose] public section

namespace NadelVanishingSeparation.NSI

theorem nadelVanishingAndNonKltDivisor : GlobalTheory.Published.NadelVanishingAndNonKltDivisor :=
  ⟨nadelVanishingPair, isolatedNonKltDivisor⟩

end NadelVanishingSeparation.NSI
