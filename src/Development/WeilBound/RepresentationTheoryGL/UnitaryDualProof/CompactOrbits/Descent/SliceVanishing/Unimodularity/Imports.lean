module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.UnimodOfIndexSym
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.RelIndexLatConj

@[expose] public section

namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unimod [CharZero k] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) :=
  unimod_of_indexSym PositivityTheory.RgUd.T.Desc.SLT.indexSym

end PositivityTheory.RgUd.T.Desc.SLF.Un2
