module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.UntwZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.EtaleChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.LineUnitCm
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma

@[expose] public section

namespace UpperTheory.Gal.KunnethLefschetz.Di

theorem steps : Steps :=
  ⟨ringL_holds, geoPB_holds, geoM_holds, first_chern_class_isBaseChange, rootNat_holds, powRoot_holds, untw_holds, pBLim_holds, pBQOf_holds,
    diagSq_holds, clear_holds, G.blowBC, G.blowE, G.pBE⟩

theorem diagEt2_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt2 := steps.diagEt2 hI hQ

theorem diagEt3_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt3 := CrystallineSemistableComparison.Onto.diagEt3_of (diagEt2_of hI hQ)

end UpperTheory.Gal.KunnethLefschetz.Di
