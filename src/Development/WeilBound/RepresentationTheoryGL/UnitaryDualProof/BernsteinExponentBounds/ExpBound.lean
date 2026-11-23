module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.BesselSum
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCell
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ExpBoundOf

@[expose] public section

namespace PositivityTheory.RgUd

theorem expBound (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : ExpBound k :=
  Exp.Final.expBound_of k (Cell.expLow k (Form.Final.besselSum k) (Cell.openCell k))

end PositivityTheory.RgUd
