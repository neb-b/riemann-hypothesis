module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormWindow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormWindow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ Convex ℝ B ∧ A w ∈ B ∧
        IsOpen N' ∧ closure W ⊆ N' ∧ (∀ i, AnalyticOnNhd ℂ (f i) N') ∧
        X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} ∧
        (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) ∧
        (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ i, ∀ z ∈ X ∩ W, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) ∧
        (∀ j, AnalyticOnNhd ℂ (a j) B) ∧ AnalyticOnNhd ℂ δ B ∧ (∀ i j, AnalyticOnNhd ℂ (q i j) B) ∧
        (∀ y ∈ B, δ y ≠ 0 →
          (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ K, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ C * r ^ (2 * d)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → IsSheetAt J A x s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s) (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFixedBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J →
      ∃ M : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ M

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → Continuous f → HasCompactSupport f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → ℂ) (ε : ℝ), 0 < ε →
        ∀ v w : (Fin n → ℂ) → ℝ, (∀ x, 0 ≤ w x) → (∀ x ∈ tsupport f, |v x| ≤ w x) →
          ∀ y, chartAbsDens J A (fun x => v x * f x) (vecCons (logReg u ε) φ) y ≤
            C * chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def euclBall {n : ℕ} (x : Fin n → ℂ) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {y | Real.sqrt (euclPot (y - x)) < ρ}

theorem mem_euclBall_iff {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by
  rw [EuclideanSpace.dist_eq]
  simp [euclBall, euclPot, dist_eq_norm]

theorem mem_euclBall_self {n : ℕ} (x : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : x ∈ euclBall x ρ := by
  simp [euclBall, euclPot, hρ]

def RegLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y ≤
        r ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLogDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def logDistSq {n : ℕ} (x : Fin n → ℂ) (z : Fin n → ℂ) : ℝ :=
  Real.log (euclPot (z - x))

def RegLogDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → z ≠ x → IsSheetAt J A z s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => logDistSq x : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s)
        (A *ᵥ z)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularInjectivePieces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegularInjectivePieces.Statement : Prop :=
  ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin d → ℂ), IsOpen U → DifferentiableOn ℂ g U →
    ∃ P : ℕ → Set (Fin d → ℂ), (∀ i, MeasurableSet (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      ⋃ i, P i = {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
      ∀ i, Set.InjOn g (P i)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetAreaCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

def SheetAreaCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ h : (Fin n → ℂ) → ℝ, Measurable h →
      ∫⁻ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ ≤
        c * ∫⁻ z in zeroSetEuc J, ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetImageArea
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def SheetImageArea.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
    ∀ g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable g →
      ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ z in (fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B, g z ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetImageAreaSet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def SheetImageAreaSet.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
      μH[((2 * d : ℕ) : ℝ)] ((fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B) =
        ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

