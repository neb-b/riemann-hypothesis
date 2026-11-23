module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Closed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftCHolds
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists

@[expose] public section

namespace UpperTheory.Gal.ToralGalois.R2

theorem toTor_holds : ToTor :=
  toTor UpperTheory.Gal.InertialTypesAlt.suppBC_outright UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrField_holds UpperTheory.Gal.NearKilling.allLift_holds UpperTheory.Gal.NearKilling.ineNorm
    (infLifts (infStep UpperTheory.Gal.InertialTypesAlt.stableOf)) (recChars UpperTheory.Gal.InertialTypesAlt.suppIne) UpperTheory.Zero.LLC.recTExists

theorem localGlobalCompatAtIwahoriFixed_of_unlinked : GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := r2g mixedOf toTor_holds drDesc UpperTheory.Zero.LLC.recTExists

end UpperTheory.Gal.ToralGalois.R2
