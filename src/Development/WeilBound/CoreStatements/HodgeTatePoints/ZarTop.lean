module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ZarhinStatementOfDualCubeQiR
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds

@[expose] public section

namespace PositivityTheory.HtPt.Narrow

theorem zarhin (hD : GlobalTheory.Published.DualAbelianScheme) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  PositivityTheory.PrwZar.zarhinStatement_of_dual_cube hD GlobalTheory.SpreadingModels.cubeTheorem_holds

end PositivityTheory.HtPt.Narrow
