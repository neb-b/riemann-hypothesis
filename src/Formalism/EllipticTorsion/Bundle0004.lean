module

public import Mathlib
public import Formalism.EllipticTorsion.Bundle0003
public import Formalism.EllipticTorsion.WChordSeries

@[expose] public section

-- bundled from Formalism.EllipticTorsion.EllipticTorsionWeights
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def EllipticTorsionWeights : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 →
    ∀ (F : FormalGroup (unitBall K)) (l E g : PowerSeries K) (ζ : K),
      IsLog (FK F) l → constantCoeff E = 0 → E.subst l = X → l.subst E = X →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((p : ℝ) ^ 2 - 1))) →
      ζ ^ (p ^ 2 - 1) = 1 → (∀ m : ℕ, ¬ (p ^ 2 - 1) ∣ m → ‖ζ ^ m - 1‖ = 1) →
      IsHom (FK F) (FK F) (ζ • X) →
      constantCoeff g = 0 →
      IntegralMv (g.subst (FK F).toPowerSeries - atX g - atY g) →
      IntegralPS (g.subst (ζ • X : PowerSeries K) - ζ ^ p • g) →
      ‖coeff 1 g‖ ≤ 1 →
      ∀ n : ℕ,
        ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / ((p : ℝ) ^ 2 - 1)) ∨
        (∃ j : ℕ, Odd j ∧ n = p ^ j ∧
          ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / ((p : ℝ) ^ 2 - 1)))

def FrobExpand : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime → ‖(p : K)‖ < 1 →
    ∀ (m j : ℕ) (a b : Fin m → K), (∀ e, ‖a e‖ ≤ 1) → (∀ e, ‖a e ^ (p ^ j) - b e‖ ≤ ‖(p : K)‖) →
      ∀ α : Fin m →₀ ℕ,
        ‖AddMonoidAlgebra.coeff ((∑ e, MvPolynomial.C (a e) * MvPolynomial.X e) ^ (p ^ j)
              - (∑ e, MvPolynomial.C (b e) * MvPolynomial.X e ^ (p ^ j)))
            α‖ ≤ ‖(p : K)‖

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.FormalGroupPointsParametrisation
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def evalPS {K : Type u} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, coeff n f * t ^ n

def evalMv2 {K : Type u} [NormedField K] (F : MvPowerSeries (Fin 2) K) (a b : K) : K :=
  ∑' d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F * a ^ (d 0) * b ^ (d 1)

def uOf {K : Type u} [Field K] {W : WeierstrassCurve K} : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => -x / y

def FormalGroupPointsParametrisation : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K), IntegralModel W → WFixed W w →
    (∀ t : K, 0 < ‖t‖ → ‖t‖ < 1 →
      evalPS w t ≠ 0 ∧ W.toAffine.Nonsingular (t / evalPS w t) (-1 / evalPS w t) ∧
        1 < ‖t / evalPS w t‖ ∧ -(t / evalPS w t) / (-1 / evalPS w t) = t) ∧
    (∀ (x y : K), W.toAffine.Nonsingular x y → 1 < ‖x‖ →
      0 < ‖-x / y‖ ∧ ‖-x / y‖ < 1 ∧
        x = (-x / y) / evalPS w (-x / y) ∧ y = -1 / evalPS w (-x / y))


open scoped Classical in
open Classical in
def FormalGroupPointsHomomorphism : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K) (F₂ : MvPowerSeries (Fin 2) K),
    IntegralModel W → WFixed W w → IntegralMv F₂ → MvPowerSeries.constantCoeff F₂ = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → uOf (P + Q) = evalMv2 F₂ (uOf P) (uOf Q)

end Formalism.ELL
end
end

