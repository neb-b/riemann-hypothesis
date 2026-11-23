module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.Bundle0002

@[expose] public section

namespace CrystallineSemistableComparison.Onto

theorem chartLaws_pf : ChartLaws := by
  intro K _ W Z Y q i _ π d V c
  obtain ⟨h1, h2, h3⟩ := chartLaws_A K W Z Y q i π d V c
  exact ⟨h1, h2, h3, fun k D h hD => chartLaws_B K W Z Y q i π d V c k D h hD⟩

end CrystallineSemistableComparison.Onto
