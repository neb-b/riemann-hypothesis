module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementF
public import Formalism.MahlerMeasure.Bundle0008
public import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0002
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
public import Formalism.PolynomialDimension.MultinomialDepth.MonoCount
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
public import Formalism.PolynomialDimension.MultinomialDepth.TieOps
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound

@[expose] public section

namespace Formalism.InvariantFactorPaths.MC

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.TM

def GamIntC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ PolZ p r LL → f' ∈ PolZ p r LL →
    ∃ c : ℕ → ℤ_[p], ∀ n, LL.total ≤ n →
      ((p : ℚ_[p]) ^ ((N + 4) * (r * Nat.log p (LL.total + LL.deg (Fin.last N) + r)) +
          6 * Nat.log p (LL.total + LL.deg (Fin.last N) + r))) * tieGam p LL ρ z n f f' =
        ∑ i ∈ range (LL.total + LL.deg (Fin.last N) + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])

def YPartnerC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → HypP p LL ρ e1 →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) ≤ ‖fockN p LL z z''‖

end Formalism.InvariantFactorPaths.MC
