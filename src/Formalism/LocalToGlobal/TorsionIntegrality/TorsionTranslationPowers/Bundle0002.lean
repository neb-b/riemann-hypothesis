module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
section
noncomputable section

namespace Formalism.L2.Th1.E

def CMIntegrality : Prop :=
  ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
    ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1


open Classical in
def ScaledTorsionPointNonsingular : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (Formalism.L2.Th1.A.shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementN
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

section Four

variable {K : Type} [Field K]

def tensor4 {n : Type} (Θ : MvPowerSeries n K) : MvPowerSeries (Fin 4 × n) K :=
  ∏ a : Fin 4, MvPowerSeries.subst (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) Θ

def matCoord {O m : Type} [Semiring O] [Fintype m] (l linv : PowerSeries K) (τ : O →+* K)
    (γ : Matrix m m O) (w : m) : MvPowerSeries m K :=
  Formalism.L2.Th1.C.flin l linv (fun w' => τ (γ w w')) (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))

end Four

def FourthPower : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (n : Type) (f : MvPowerSeries n K),
    Integral (tensor4 f) → Integral f

def ThetaFourthTensorPowerProductShape {K : Type} [NormedField K] [CharZero K] {O n : Type} [Semiring O] [Fintype n]
    (l linv ph : PowerSeries K) (τ : O →+* K) (Θ : MvPowerSeries n K) (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) :
    Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (r : κ → K) (V : κ → Fin 4 × n → PowerSeries K),
    (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k w, IntS (V k w)) ∧
    MvPowerSeries.subst (matCoord l linv τ γ) (tensor4 Θ) =
      thetaProd r (fun k w => (mvExp (-ph) : PowerSeries K) * V k w)

def GeneralIntOf : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (l linv ph : PowerSeries K), Formalism.L2.Th1.C.Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R l linv ph →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (Θ : MvPowerSeries n K)
      (γ : Matrix (Fin 4 × n) (Fin 4 × n) O), γ.conjTranspose * γ = 1 →
      ThetaFourthTensorPowerProductShape l linv ph τ Θ γ → Integral (mvExp (phSum ph : MvPowerSeries n K) * Θ)

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementS
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def IsShiftSys {K : Type} [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (A : AddSubgroup W.toAffine.Point) (S : W.toAffine.Point) (H : W.toAffine.Point → K⟦X⟧)
    (c : W.toAffine.Point → K) : Prop :=
  OneUnit (H 0) ∧ (∀ Q ∈ A, Q ≠ 0 → c Q ≠ 0) ∧
  ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → ∃ ρ : K, ‖ρ‖ = 1 ∧
    H (P + Q) * H (P - Q) = C (ρ * c Q ^ 2) * (C (px W Q) - xT W (P + S)) * H P ^ 2

def ShiftUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A →
    (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) →
    (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1) →
    ∀ (H : W.toAffine.Point → K⟦X⟧) (c : W.toAffine.Point → K), IsShiftSys W A S H c →
      (∀ Q ∈ A, Q ≠ 0 → ‖c Q‖ = 1) ∧
      ∀ P ∈ A, ‖constantCoeff (H P)‖ = 1 ∧ OneUnit (C (constantCoeff (H P))⁻¹ * H P)

def ShiftPtsInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A → S + S = 0 → ‖px W S‖ ≤ 1 → ‖py W S‖ ≤ 1 →
      (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) ∧
      (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1)

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementV
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def VIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ε : ℂ_[l], ‖ε‖ = 1 → (∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      IntS (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.D.phFF l (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε) *
        (PowerSeries.map (ι : ℂ →+* ℂ_[l])
          (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
          (C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l))

end Formalism.L2.Th1.E
end
end

