module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem harishChandraModules : GlobalTheory.Published.HarishChandraModules :=
  CompanionTheory.D.gk.HC.print_harishChandraModules

theorem greenCuspidal : GlobalTheory.Published.GreenCuspidal :=
  PositivityTheory.GreenCharacters.greenCuspidal

end PositivityTheory.Stage1.PM
