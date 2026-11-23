module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerVan
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSumSm
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DNearCusp

@[expose] public section

namespace MainStatements.WeightKernel.Dec

theorem decay_holds : Decay :=
  decay (core derMem (derVan smOf derMem) level (sumSm smOf) variation nearCusp base) bridge

end MainStatements.WeightKernel.Dec
