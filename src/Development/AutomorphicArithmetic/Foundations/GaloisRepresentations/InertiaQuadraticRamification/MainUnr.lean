module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.OrdPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharPP

@[expose] public section

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem unrSplit_holds : UnrSplit :=
  unrSplit_of groupStep (unrCharPP (ordPrime (kumMove moveRoot normVal)) charOrd decPow) (freshSplit freshChar_holds) exFld
    layerOf_holds degOf splitIff

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
