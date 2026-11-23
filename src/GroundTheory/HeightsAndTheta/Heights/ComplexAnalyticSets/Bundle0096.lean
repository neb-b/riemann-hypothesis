module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermProjectionStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PrimeGermProjectionStep.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime → P ≠ ⊥ →
    (∀ (τ : Type) [Fintype τ], Fintype.card τ < Fintype.card σ →
      ∀ (v : τ → ℂ) (Q : Ideal (holGerms v)), Q.IsPrime →
        ∃ (d : ℕ) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection v Q B) →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchInOneBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchInOneBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q)
    (ν : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∃ b, ∃ ρ' > 0, ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ' → ν.toFun (fun _ ↦ τ) ∈ (c b).image

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchSameOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchSameOrder.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c d : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) →
      ∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder d f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCurveDiscInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedCurveDiscInverse.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ (φ : ℂ → Fin n → ℂ) (σ₀ : ℂ) (δ : ℝ), 0 < δ →
      DifferentiableOn ℂ φ (Metric.ball σ₀ δ) → Set.InjOn φ (Metric.ball σ₀ δ) →
      Set.MapsTo φ (Metric.ball σ₀ δ) (zeroSet I) → φ σ₀ ∈ Metric.ball q ε → φ σ₀ ≠ q →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ φ σ₀ ∈ U ∧ ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ U ∧
        ∀ z ∈ zeroSet I ∩ U, ∃ σ ∈ Metric.ball σ₀ δ, φ σ = z ∧ ψ z = σ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegRadialWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def radialTransform (d : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * t ^ d - ∫ τ in (0 : ℝ)..t, a τ * ((d : ℝ) * τ ^ (d - 1))

theorem radialTransform_zero (a : ℝ → ℝ) : radialTransform 0 a = a := by
  funext t
  simp [radialTransform]

theorem integral_const_mul_dpow (e : ℕ) (c t : ℝ) :
    ∫ τ in (0 : ℝ)..t, c * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) = c * t ^ (e + 1) := by
  simp only [Nat.add_sub_cancel]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

theorem radialTransform_eq_zero_of_const (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by
  have hint : ∫ τ in (0 : ℝ)..t, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ∫ τ in (0 : ℝ)..t, a 0 * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    rw [ha τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  rw [radialTransform, hint, integral_const_mul_dpow, ha t ht]
  ring

def RegRadialWeight.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * ((d : ℝ) * τ ^ (d - 1))) = 0 →
      ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => radialTransform d a (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrderBranchesMeet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def SameOrderBranchesMeet.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c c' : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder c' f) →
      ∃ x ∈ c.image ∩ c'.image, x ≠ q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

def SliceCMUnmixed.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ),
    IsCohenMacaulayAt J q → ringKrullDim (localRingAt J q) = (d + 1 : ℕ) →
    ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ) →
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
        P ≤ RingHom.ker (eval q) →
          P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def SliceLocalDimGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
        ∀ L ∈ O, ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimUpperZariski
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceLocalDimUpperZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
        ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
          ringKrullDim (localRingAt (sliceIdeal J L q) q) ≤ (1 : ℕ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceUnmixedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ)
              (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
            P ≤ RingHom.ker (eval q) →
              P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseSliceGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def TransverseSliceGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        IsOpen {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} ∧
          Dense {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q}

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongAnnulus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y) -
        s ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y) =
      r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

