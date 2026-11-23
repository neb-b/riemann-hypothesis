module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.StageC
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoReducibleC
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

@[expose] public section

namespace CompanionTheory.RgGu

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness CompanionTheory.Geo.geometricLemmaFiltration
  SRC.segRep_of SRC.stageP hG (SRC.segTwo_of hG NR.rhoNuRhoReducibleC)

end CompanionTheory.RgGu
