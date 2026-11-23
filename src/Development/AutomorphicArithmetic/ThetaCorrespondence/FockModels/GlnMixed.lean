module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.IsZSegDetRep

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace UpperTheory.Lit.Mix

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_unconditional

theorem polynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation
    (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mixed {r : ℕ} (t : ℕ) {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  UpperTheory.Lit.Full.top geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds polynomialRing k r t V π χ s i u hs hu

theorem prod₂_detRep' (_H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible := mixed t s i u hs hu

end UpperTheory.Lit.Mix

end
