module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PolynomialKilling.KillPoly4

@[expose] public section

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Rs.JKillPoly

end JKillPoly

open JKillPoly in
theorem killPoly_holds : KillPoly := KillingPolynomialDegreeFour.killPoly4

end PositivityTheory.Rg.Rs

end
