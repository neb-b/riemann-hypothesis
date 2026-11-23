module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG

@[expose] public section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.PW MvPolynomial Finset

def TrivProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]),
    j ≤ 1 → 1 ≤ r → IsTypeProj p LL j univ T P → (∀ F ∈ Pol p r LL, P F = F) ∨ (∀ F ∈ Pol p r LL, P F = 0)

def HighestVectorProjectionPos : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    1 ≤ K → 2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ ((K + 1) * e1)) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)

def GradedBoundOfSaturationPos : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 c0 : ℕ) (κ : ℝ),
    1 ≤ K → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e ≤ LLw.deg (Fin.last K), ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) →
    (((K + 3) * e1 + 2 * c0 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ

def ResSatLZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) [NeZero r] (LL : Letters (0 + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last 0) = true → ResSatL p LL J M ρ 0

end Formalism.InvariantFactorPaths.L4
