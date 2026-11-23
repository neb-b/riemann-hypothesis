module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.RgGu

theorem irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n V _ _ π hs hi => (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem prodIrrFiniteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.ProdIrrFiniteLength k :=
  fun _ _ _ _ _ _ _ x hd => GlobalTheory.T.product_irreducible_finite_length irreducibleAdmissibleGL x hd

end GlobalTheory.RgGu

end
