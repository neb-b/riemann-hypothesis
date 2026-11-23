module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds

@[expose] public section

open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem siegel_mass_ratio : SiegelMassRatioThm := Formalism.HermitianLattices.Ext.L3.siegelMassRatio

end Formalism.HermitianLattices.SiegelMassBounds
