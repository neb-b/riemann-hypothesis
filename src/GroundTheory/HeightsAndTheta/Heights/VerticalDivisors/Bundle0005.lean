module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def FiniteOrd.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      ∀ 𝔫 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) ≠ ⊤

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def SpecFirstNeField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0

end

end GroundTheory.Heights₂.Heights.Vertical
end

