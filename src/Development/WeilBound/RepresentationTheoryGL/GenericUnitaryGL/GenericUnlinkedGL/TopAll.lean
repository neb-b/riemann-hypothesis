module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.ExistsEquivOfMapUnivEq
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Bridge

@[expose] public section

namespace GlobalTheory.RgGu

theorem genericUnique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GenericUnique k :=
  genericUnique_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (PositivityTheory.rg.gu.hered2.whitHeredity_all k)
    (PositivityTheory.rg.gu.whit.whitRankIrr k) (GlobalTheory.BZSeg.Cusp.cuspGeneric k)

end GlobalTheory.RgGu
