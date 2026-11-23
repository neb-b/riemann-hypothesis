module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecFiniteUnit.Statement : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R), IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      IsUnit (eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k R) g y)) →
        Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k R))) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionCycleReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, linForm u ∉ P) →
      fundCycle (J ⊔ Ideal.span {linForm u}) = ∑ P ∈ (fundCycle J).support, divCycle P u

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughTwoPointsTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughTwoPointsTrdeg.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (n k : ℕ) [Algebra K Ω]
    [Algebra (MvPolynomial (Fin k × Fin n) K) Ω] [IsScalarTower K (MvPolynomial (Fin k × Fin n) K) Ω],
    Function.Injective (algebraMap (MvPolynomial (Fin k × Fin n) K) Ω) →
    ∀ x c : Fin n → K, ∑ j, c j * x j = 1 →
    ∀ (y : Fin n → Ω) (j : Fin n), y j ≠ 0 → (∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m)) →
      (∀ i, ∑ m, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (genSubst x c (i, m)) * y m = 0) →
        (k : Cardinal) ≤ Algebra.trdeg K (Algebra.adjoin K (Set.range fun m => y m * (y j)⁻¹))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

