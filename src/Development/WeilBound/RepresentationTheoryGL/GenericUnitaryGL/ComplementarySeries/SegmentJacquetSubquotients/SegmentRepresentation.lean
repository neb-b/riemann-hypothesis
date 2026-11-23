module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.StageC
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoReducibleC
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030

@[expose] public section

namespace PositivityTheory.RgGu

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness PositivityTheory.Geo.geometricLemmaFiltration
  SRC.segRep_of SRC.stageP hG (SRC.segTwo_of hG NR.rhoNuRhoReducibleC)

end PositivityTheory.RgGu
