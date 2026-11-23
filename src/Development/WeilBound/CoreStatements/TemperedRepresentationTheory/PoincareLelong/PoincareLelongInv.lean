module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll

@[expose] public section

namespace PositivityTheory.Tls2.Pl

theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
