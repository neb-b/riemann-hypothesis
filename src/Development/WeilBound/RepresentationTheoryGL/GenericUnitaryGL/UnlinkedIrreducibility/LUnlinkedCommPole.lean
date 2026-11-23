module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

@[expose] public section

noncomputable section

namespace GlobalTheory.RgGu.Unl

theorem lUnlinkedIrr_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  exact lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)
    PositivityTheory.Geo.geometricLemmaFiltration (PositivityTheory.RgGu.NR.nuPair k)

theorem lUnlinkedComm_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedComm k :=
  fun k _ _ _ _ => lUnlinkedComm_of_irr k (lUnlinkedIrr_pole hZ k)

end GlobalTheory.RgGu.Unl

end
