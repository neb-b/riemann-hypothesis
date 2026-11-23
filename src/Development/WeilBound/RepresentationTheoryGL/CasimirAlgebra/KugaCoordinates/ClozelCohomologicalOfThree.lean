module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomologicalOfRest
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KugaAbsHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CasBoundHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CoefficientGluing.CoefGlueHolds

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_three (hw : WhitLie) (hkg : KugaGlue) (hco : Cochain) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of_rest kType_holds GK.gkData_holds hw kugaAbs_holds hkg coefGlue_holds hco casBound_holds

end PositivityTheory.Rg.Cz
