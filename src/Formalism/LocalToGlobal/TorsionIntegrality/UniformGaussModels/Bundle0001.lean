module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)

def thetaZ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (ω₀ : ℂ)
    {κ n : Type} [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ) : MvPowerSeries n ℂ_[p] :=
  Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.map (ι : ℂ →+* ℂ_[p])
    (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L (s k i) (Formalism.L2.Th1.F.th0 L (ω₀ / 2)))))

def phC (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) : PowerSeries ℂ_[p] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (wpReg (curveL p L ι)) (logSer (curveL p L ι))

def GoodModelAll : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (c : ℂ) (hc : c ≠ 0), IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)

def CMDatum : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), IntCurve (curveL p L ι) →
  ∀ m n : ℤ, ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n →
  ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
    Formalism.L2.Th1.C.IsEndoCurve (curveL p L ι) neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK dK)) ∧
    (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (Fintype.card S : ℂ_[p]) + 1 ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) *
        (ι ((m : ℂ) + (n : ℂ) * omegaK dK) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
        ι (Formalism.L2.Th1.F.s2 L) = ∑ P, (xP P + (curveL p L ι).b₂ / 12)

def ShapeCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.G.ShapeAt (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) dK

def JetsCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    ∀ i : ℕ, 1 ≤ i → ‖Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) i‖ ≤ 1

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

def PhMap : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] [CharZero K] [CharZero K'] (φ : K →+* K') (l : ℕ), 2 ≤ l →
    ∀ g2 g3 s2 ε : K,
      PowerSeries.map φ (phFF l g2 g3 s2 ε) = phFF l (φ g2) (φ g3) (φ s2) (φ ε)

def CalcC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ ≤ 1 → σ (σ α) = α →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l]) ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l])) ∧
    (∀ z : MaximalUnramifiedExtension l, ‖z‖ ≤ 1 → σ z = z → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[l]) (z : ℂ_[l]))

end Formalism.L2.Th1.Top
end
end

