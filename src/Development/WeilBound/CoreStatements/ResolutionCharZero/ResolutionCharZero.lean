module

public import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
public import Development.WeilBound.CoreStatements.ResolutionCharZero.ResolutionCharZeroOfTop

@[expose] public section

namespace PositivityTheory.Resplug.ResolutionBlowup

theorem resolutionCharZero : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero :=
  resolutionCharZero_of_top FunctorialResolution.functorialResolutionCharZero.{0}

end PositivityTheory.Resplug.ResolutionBlowup
