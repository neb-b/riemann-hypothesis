module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.DivisionOneGeometricRepresentation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0005

@[expose] public section

namespace UpperTheory.Gal.Int.Div

theorem seedFinOdd_of_geoOne (h : UpperTheory.Gal.Int.Geo.GeoOne) : GlobalTheory.CongL.SeedFinOdd :=
  seedFinOdd_of divAll_holds cplMem_of (sameOr_of cplMem_of) (satConj_of locIso_of) (tyConj_of locIso_of) (lacConj_of cplMem_of)
    gapLac_of dGenMul_of h

end UpperTheory.Gal.Int.Div
