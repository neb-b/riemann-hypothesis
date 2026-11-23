module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjDegreeChow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjDegreeChow.Statement : Prop :=
  ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ComplexSets.IsFiniteProjection W A → ComplexSets.projDegree W A = δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights


open Classical in
def SectionLengthSum.Statement : Prop := by
  classical
  exact
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J W : Ideal A) (f : A),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    W ∈ (J ⊔ Ideal.span {f}).minimalPrimes →
    (∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) →
      GroundTheory.Heights₂.Heights.localMult (J ⊔ Ideal.span {f}) W =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing A).toFinset with P ≤ W,
          GroundTheory.Heights₂.Heights.localMult (P ⊔ Ideal.span {f}) W

end GroundTheory.Heights₂.Heights
end

