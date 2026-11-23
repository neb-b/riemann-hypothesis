module

public import Mathlib
public import Formalism.PolynomialDimension.Bundle0002
public import Formalism.PolynomialDimension.MultinomialDepth.Bundle0002
public import Formalism.PolynomialDimension.MultinomialDepth.BinomialSeriesBound
public import Formalism.PolynomialDimension.MultinomialDepth.Bundle0001
public import Formalism.PolynomialDimension.MultinomialDepth.HarmonicDecompositionHolds
public import Formalism.PolynomialDimension.MultinomialDepth.DiagLaplacianDivPowMemSqrtFockLattice
public import Formalism.PolynomialDimension.MultinomialDepth.SqrtFockGaussLatticeComparisonHolds
public import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSizeBoundsHolds
public import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSlackBoundsHolds
public import Formalism.PolynomialDimension.Bundle0001

@[expose] public section

-- bundled from Formalism.PolynomialDimension.DigitClassCount
section
namespace Formalism.CountingSumsFrames.Top

theorem levelCount : Formalism.CountingSumsFrames.LevelCount := Formalism.CountingSumsFrames.harmonic_level_count
theorem densityLower : Formalism.CountingSumsFrames.DensityLower := Formalism.CountingSumsFrames.density_lower_bound

end Formalism.CountingSumsFrames.Top
end

-- bundled from Formalism.PolynomialDimension.FinalHar
section
namespace Formalism.CountingSumsFrames.Top

theorem slTwo : Formalism.CountingSumsFrames.SlTwo := Formalism.CountingSumsFrames.slTwoCommutator_holds
theorem harProj : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.harmonicProjection_holds
theorem levelProj : Formalism.CountingSumsFrames.LevelProj := Formalism.CountingSumsFrames.isotypicProjection_holds
theorem gaussProj : Formalism.CountingSumsFrames.GaussProj := Formalism.CountingSumsFrames.gaussLatticeProjection_holds
theorem gaussLemmaH : Formalism.CountingSumsFrames.GaussLemmaH := Formalism.CountingSumsFrames.gaussLemmaPairing_holds
theorem levelLattice : Formalism.CountingSumsFrames.LevelLattice := Formalism.CountingSumsFrames.isotypicLattice_holds
theorem harQuot : Formalism.CountingSumsFrames.HarQuot := Formalism.CountingSumsFrames.harmonicQuotient_holds

end Formalism.CountingSumsFrames.Top
end

-- bundled from Formalism.PolynomialDimension.FinalNum
section
namespace Formalism.CountingSumsFrames.Top

theorem paramsII0 : Formalism.CountingSumsFrames.ParamsII0 := Formalism.CountingSumsFrames.secondParameterSizeBounds_holds
theorem paramsII5 : Formalism.CountingSumsFrames.ParamsII5 := Formalism.CountingSumsFrames.secondParameterSlackBounds_holds

end Formalism.CountingSumsFrames.Top
end

