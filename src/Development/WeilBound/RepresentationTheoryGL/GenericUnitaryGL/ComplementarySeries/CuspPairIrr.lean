module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563

@[expose] public section

namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nuPair : GlobalTheory.BZSeg.NuPair k :=
  nuPair_of k (GlobalTheory.T.derivative_jacquet_holds k GlobalTheory.CompanionTheory.BZCuspPair.irrAdm) (jmTheta k) (derFin_of k (derEquiv k))

theorem cuspPairIrr : GlobalTheory.BZSeg.CuspPairIrr k := cuspPairIrr_of k (nuPair k)

end PositivityTheory.RgGu.NR
