module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffTube
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffTube.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ i, SmoothNear (zeroSet J) (φ i)) → Integrable (tubeDens J A P R φ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGoodPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    q ∈ zeroSet J → linEval u q = 0 → DivisorRegularAt J u d q → NormalDivisorChartAt M u d q →
    NormalDoublePointsOnDivisor M u q →
      ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
          (π : Matrix (Fin d) (Fin n) ℂ),
          (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
          (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
          (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
          (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
          ∀ b, Function.Bijective
            (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorOneComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def DivisorOneComponent.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorRegularGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorRegularGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → DivisorRegularAt J u d q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreSectionsCovering
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

def FibreSectionsCovering.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (Ω : Set (Fin (e + 1) → ℂ))
    (X : Set (Fin n → ℂ)) (hX : Set.MapsTo (fun x => A *ᵥ x) X Ω),
    (∀ y ∈ Ω, {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    IsCoveringMap hX.restrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitAtBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ) (π : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → q ∈ zeroSet W →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
    (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
    (∀ b, Function.Bijective
      (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))) →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (((∑ b, ord b : ℕ) : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitGoodPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitGoodPoints.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
            Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
              (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
                  (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
                (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitOffZero.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    Disjoint (tsupport f) (zeroSet J ∩ {x | linEval u x = 0}) →
      Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0) (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOnZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitOnZero.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (p : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → p ∈ zeroSet J → linEval u p = 0 →
      ∃ N ∈ 𝓝 p, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → J ⊔ Ideal.span {linForm u} ≤ I →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ δ > 0, ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ) ∧
        |∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

