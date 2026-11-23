module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.DerivSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

@[expose] public section

namespace GlobalTheory.RgGu.Nup2

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.NuPair k := fun k _ _ _ _ =>
  _root_.GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.T.derivative_jacquet_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (_root_.GlobalTheory.CompanionTheory.JmThetaInv.jmTheta k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (derivSub_main k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)

end GlobalTheory.RgGu.Nup2
