module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.GramExists
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

def GramExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ (E : Type) [Fintype E] [DecidableEq E],
      ∃ c : Bool × E → Bool × E → K,
        (∀ k x, ‖c k x‖ ≤ 1 ∧ σ (σ (c k x)) = c k x) ∧
        ∀ x x' : Bool × E, ∑ k, c k x * σ (c k x') = if x.1 ≠ x'.1 ∧ x.2 = x'.2 then 1 else 0

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RingAFacts
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def RingAFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x ∈ ringA l, ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y)

def FrobA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ σ0 : ringA l →+* ringA l,
      (∀ ζ : ringA l, (ζ : ℂ_[l]) ∈ muPrime l → σ0 ζ = ζ ^ l) ∧
      ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y

def FrobAIsom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ0 : ringA l →+* ringA l),
    (∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) →
    ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)

section Defs

variable {K : Type} [Field K]

def thetaS (l : ℕ) (g2 g3 ε : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C ε * lgF K l) (Formalism.L2.Th1.CM.uSer g2 g3)

variable [CharZero K]

def phFF (l : ℕ) (g2 g3 s2 ε : K) : PowerSeries K :=
  -PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3))) +
    PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 -
    Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))

def phCurve (g2 g3 s2 : K) : PowerSeries K :=
  Formalism.L2.Th1.B.phO s2 (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))

end Defs

def LtLogIsLgF : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l → Formalism.L2.Th1.CM.ltLog K l = lgF K l

def ThetaHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ g2 g3 ε : K,
    PowerSeries.subst (thetaS l g2 g3 ε) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) =
      PowerSeries.C ε * lgF K l ∧
    IsHom F (Formalism.L2.Th1.A.fgl (Formalism.L2.Th1.A.shortW g2 g3)) (thetaS l g2 g3 ε)

def PhCompare : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ∀ g2 g3 s2 ε : K, ‖ε‖ = 1 → (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
    Simeq (phFF l g2 g3 s2 ε : MvPowerSeries Unit K)
      (PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2))

def CurveExponentCoboundaryCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → 2 < l →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ g2 g3 s2 ε : K, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
      F1 F (cob F (phFF l g2 g3 s2 ε))

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementN
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq)

def ChainNonVacuous : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l → ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be)

end Formalism.L2.Th1.D
end
end

