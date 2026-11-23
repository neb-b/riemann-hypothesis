module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalSpreadOfLocalExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

namespace PositivityTheory.JsR

theorem localExpBound_holds : LocalExpBound := by
  intro k _ _ _ _ _ N V _ _ π hs hi hu hg
  obtain ⟨h, δ, Δ, s, hΔ, hc, hb, hd⟩ := PositivityTheory.RgUd.Exp.genUnitCCOf PositivityTheory.RgUd.expBound GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
    k N V π hs hi hu hg
  exact ⟨h, δ, Δ, s, hΔ, fun j _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u (hΔ j) (hc j) hω z, hb, hd⟩

end PositivityTheory.JsR
