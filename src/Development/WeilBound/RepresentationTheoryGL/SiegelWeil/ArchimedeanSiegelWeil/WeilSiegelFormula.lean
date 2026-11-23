module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelDeg

@[expose] public section

theorem PositivityTheory.Rg.Wsf.weilSiegelFormula : GlobalTheory.Published.WeilSiegelFormula :=
  PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg
