module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem geoOne_of_parts (h₁ : Steps) (h₂ : KSAll) (h₃ : PlanEx) : GeoOne := geoOne_of h₁ (packEx_of h₂ h₃)

end UpperTheory.Gal.Int.Geo
