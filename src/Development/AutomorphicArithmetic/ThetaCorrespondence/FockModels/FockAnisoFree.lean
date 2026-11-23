module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoOfRanges
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CoefND
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.WeilSiegelFormula
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SiegelFormulaSchwartz.SiegelFormulaThetaOfSchwartz
public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta

@[expose] public section

namespace UpperTheory.Lit.Sw47

theorem convergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent := GlobalTheory.StdUnn.sw_doubled_of_std PositivityTheory.SiegelWeilCoefficients.field

theorem weilUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary :=
  PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two UpperTheory.Lit.weilThetaConvergence PositivityTheory.Rg.Wsf.weilSiegelFormula

theorem fa : FA := fa_of convergent weilUnitary

theorem fockAniso_free (_ : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D

end UpperTheory.Lit.Sw47
