module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.ProdFL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

@[expose] public section

noncomputable section

namespace GlobalTheory.RgGu.Unl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitRankStd : GlobalTheory.BZSeg.WhitRankStd k :=
  _root_.GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k)

theorem lUnlinkedIrr_nu (hJ : Zc.LSegJacquet k) (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hN : GlobalTheory.BZSeg.NuPair k) :
    GlobalTheory.BZSeg.LUnlinkedIrr k := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  have hF : GlobalTheory.BZSeg.ProdIrrFiniteLength k := by
    first
    | exact GlobalTheory.RgGu.prodIrrFiniteLength k
    | exact fun h N x hd => GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  exact _root_.GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr k hA hJ hG hN (whitRankStd k) hF

theorem lUnlinkedComm_of_irr (hL : GlobalTheory.BZSeg.LUnlinkedIrr k) : GlobalTheory.BZSeg.LUnlinkedComm k :=
  _root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k GlobalTheory.RgGu.irreducibleAdmissibleGL hL

end GlobalTheory.RgGu.Unl

end
