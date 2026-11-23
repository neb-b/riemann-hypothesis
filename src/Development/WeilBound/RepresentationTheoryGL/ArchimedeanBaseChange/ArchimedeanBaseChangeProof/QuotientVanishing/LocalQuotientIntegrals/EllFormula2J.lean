module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuotNormaliserIndicator

@[expose] public section

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.D4

theorem classVanish2 : ClassVanish2 := classVanish2_of (GlobalTheory.CompanionTheory.SliceFubini.sliceTerm_of mahler) classVanish sizeBasic

theorem ellFormula2J : EllFormula2J := ellFormula2_of (GlobalTheory.CompanionTheory.TwUnfold.unfold2_of mahler) ellTerm classVanish2 sizeBasic

end PositivityTheory.Rg.BcB.CV
