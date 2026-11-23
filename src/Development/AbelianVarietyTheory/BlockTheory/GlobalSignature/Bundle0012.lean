module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AbsoluteLogMeanBounds
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients Classical

def kronBound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt (D.host.d : ℝ)) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

end GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic

open Complex GlobalTheory.Glob.IntegralWittCoefficients

def IsPeriodLattice (Λ : AddSubgroup ℂ) (ω₁ τ : ℂ) : Prop :=
  ∀ x : ℂ, x ∈ Λ ↔ ∃ m n : ℤ, x = ω₁ * ((m : ℂ) + (n : ℂ) * τ)

def thetaChar (a b : Fin 2) (z τ : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
      (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (z + ((b : ℕ) : ℂ) / 2)) *
    jacobiTheta₂ (z + (((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ

def IsEvenChar (a b : Fin 2) : Prop := (a : ℕ) * (b : ℕ) = 0

def NormTheta0 : Prop :=
  ∀ (Λ : AddSubgroup ℂ) (ω₁ τ t₀ : ℂ), ω₁ ≠ 0 → 0 < τ.im → IsPeriodLattice Λ ω₁ τ →
    2 * t₀ ∈ Λ → t₀ ∉ Λ →
    (∃! c : Fin 2 × Fin 2, IsEvenChar c.1 c.2 ∧ thetaChar c.1 c.2 (t₀ / ω₁) τ = 0) ∧
    0 < normSq1 Λ (th0 Λ t₀) ∧
    ∀ a b : Fin 2, IsEvenChar a b → thetaChar a b (t₀ / ω₁) τ = 0 →
      (normSq1 Λ (th0 Λ t₀))⁻¹ = Real.sqrt (2 * τ.im) * ‖thetaChar a b 0 τ‖ ^ 2

theorem thetaChar_eq_tsum (a b : Fin 2) (z τ : ℂ) :
    thetaChar a b z τ = ∑' n : ℤ, cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (z + ((b : ℕ) : ℂ) / 2)) := by
  unfold thetaChar jacobiTheta₂ jacobiTheta₂_term
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

theorem jacobiTheta₂_half (a b : Fin 2) (τ : ℂ) :
    jacobiTheta₂ ((((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ =
      cexp (-((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2) * thetaChar a b 0 τ := by
  unfold thetaChar
  rw [← mul_assoc, ← Complex.exp_add, zero_add, zero_add]
  have : -((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2 +
      ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (((b : ℕ) : ℂ) / 2)) = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

end GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients

def conjNormSq (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) (ρ : M →ₐ[ℚ] ℂ) (t : ℂ) : ℝ :=
  normSq1 (lamConj M ρ Λ) (th0 (lamConj M ρ Λ) t)

def meanLog (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (conjNormSq M Λ ρ (t ρ))) / (Module.finrank ℚ M : ℝ)

def meanPosLog (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, max 0 (Real.log (conjNormSq M Λ ρ (t ρ)))) / (Module.finrank ℚ M : ℝ)

def HidaSetting (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ DataIn D (tor0 D cc δ) M ∧
    ∀ ρ : M →ₐ[ℚ] ℂ, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)

def bound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def SignedMean (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t → meanLog M (lamOf D cc δ) t ≤ bound D

def MeanLeL (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L → meanLog M (lamOf D cc δ) t ≤ L

def MeanLeC (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ L → meanLog M (lamOf D cc δ) t ≤ C * L

def PosMean (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    meanPosLog M (lamOf D cc δ) t ≤ bound D + (1 / 4) * Real.log D.host.d + C

def PosMeanLeC (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ L → meanPosLog M (lamOf D cc δ) t ≤ C * L

def Theta0SignedMean : Prop :=
  (∀ D : D7, SignedMean D) ∧ (∀ D : D7, MeanLeL D) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, MeanLeC C D

def Theta0PosMean : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, PosMean C D) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, PosMeanLeC C D

def Theta0Mean : Prop := Theta0SignedMean ∧ Theta0PosMean

end GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans
end
end

