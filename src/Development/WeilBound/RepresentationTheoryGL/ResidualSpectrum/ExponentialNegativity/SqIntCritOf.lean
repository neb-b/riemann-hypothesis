module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapPairings.GapGlue
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0283
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountLeOfDvd

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem expNeg_of (h : An.Count) : ExpNeg :=
  expNegGlue_holds dict_holds (l2glue_holds h GlobalTheory.CompanionTheory.SiegelEscape.escape)

theorem sqIntCrit_of (h1 : InitBnd) (h2 : FinTr) (h3 : An.BoxVol) : SqIntCrit :=
  sqIntGlue_holds dict_holds niceAut_holds h1 h2 killPoly_holds
    (GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound)) (GlobalTheory.CompanionTheory.SlabGlue.slabGlue h3)

theorem gap_of (h1 : LatOf) (h2 : GapOp) : Gap :=
  gapGlue_holds h1 (gapAbs_of h2 GlobalTheory.CompanionTheory.GapPolyProof.gapPoly)

end PositivityTheory.Rg.Rs
