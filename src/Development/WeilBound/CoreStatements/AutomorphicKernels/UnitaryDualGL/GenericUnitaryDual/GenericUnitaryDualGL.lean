module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011

@[expose] public section

namespace PositivityTheory.Gud

theorem generic_unitary_dual_GL : True → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments →
    GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := fun _ _ _ _ _ => Fin.genericUnitaryDualGL_holds

end PositivityTheory.Gud
