module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.ZeroFreeRegion.Statement
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes NumberField








def CycSplit : Prop :=
  ∀ (N p : ℕ) (K : Type) [Field K] [NumberField K] [Algebra K (CyclotomicField N ℚ)], 0 < N → p.Prime →
    p % N = 1 % N →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
