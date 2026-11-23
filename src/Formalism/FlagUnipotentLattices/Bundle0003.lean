module

public import Mathlib
public import Formalism.FlagUnipotentLattices.Bundle0002
public import Formalism.HyperbolicPlaceProducts.Bundle0001
public import Formalism.FlagUnipotentLattices.Bundle0001
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

@[expose] public section

-- bundled from Formalism.FlagUnipotentLattices.LatticeDeterminantIndexSq
section
open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitsSquareIndex : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], (∀ w : InfinitePlace F, w.IsReal) →
    Nat.card ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range) = 2 ^ finrank ℚ F

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

-- bundled from Formalism.FlagUnipotentLattices.OmSumLong
section
noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def EmbGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (A : Submodule (𝓞 E) V) (Q : Type) [AddCommGroup Q]
    [Module (𝓞 E) Q] [Finite Q] (φ : Q →ₗ[𝓞 E] V ⧸ A), Function.Injective φ →
      ∃ s : Fin (Module.finrank E V) → Q, Submodule.span (𝓞 E) (Set.range s) = ⊤

end Formalism.HermitianLatticeCounting.S6
end
end

-- bundled from Formalism.FlagUnipotentLattices.ValuationProductBound
section
namespace Formalism.HermitianLatticeCounting.Final.S4

theorem weightedCS : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz
theorem omCount : Formalism.HermitianLatticeCounting.S4.OmCount := Formalism.HermitianLatticeCounting.P.orbit_count_formula
theorem step4 : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.Final.S4
end

