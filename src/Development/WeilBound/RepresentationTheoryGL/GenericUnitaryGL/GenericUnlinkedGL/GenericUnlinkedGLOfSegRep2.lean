module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.TopAll
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.Realize
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

@[expose] public section

namespace GlobalTheory.RgGu

theorem genericUnlinkedGL_of_segRep2 (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GenericUnlinkedGL :=
  genericUnlinkedGL_of (fun k _ _ _ _ _ => suppExists k) (fun k _ _ _ _ _ => genericUnique k)
    (fun k _ _ _ _ _ => unlinkedRealize (k := k)
      (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hZ) (GlobalTheory.RgGu.Nup2.nuPair k))

end GlobalTheory.RgGu
