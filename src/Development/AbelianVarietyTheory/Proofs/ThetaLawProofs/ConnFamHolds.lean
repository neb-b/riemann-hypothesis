module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds

@[expose] public section

namespace GlobalTheory.KeyFam

theorem connFam_holds : GlobalTheory.KeyKa.ConnFam :=
  _root_.GlobalTheory.KeyFam.connFam_of_polFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (_root_.GlobalTheory.KeyFam.polFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.thetaUnifAV_closed
      GlobalTheory.torusAlgebraic_holds)

end GlobalTheory.KeyFam
