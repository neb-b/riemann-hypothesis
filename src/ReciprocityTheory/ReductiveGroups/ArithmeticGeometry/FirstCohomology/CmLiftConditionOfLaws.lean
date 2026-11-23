module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCFinal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonLiftPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.H1

theorem cmLiftCondition_of_laws (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : ReciprocityTheory.ChartRestriction.G.DVR.PositiveValuationMaximalIdeal)
    (hTW : ReciprocityTheory.ChartRestriction.G.DVR.TWStatement) (hU : ReciprocityTheory.ChartRestriction.G.DVR.UUStatement) : OneCStatement :=
  cmLiftCondition_of_torsion hL h1c hTW hU (canonLiftFix_of_laws hL) dimSplit

end ReciprocityTheory.ChartRestriction.G.H1
