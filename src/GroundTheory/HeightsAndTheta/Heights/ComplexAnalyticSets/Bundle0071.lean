module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCutHess
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.AnForm

noncomputable section

def LogLogCutHess.Statement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ), ∃ a b : ℝ,
    |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
    hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
    hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def NormalDivisorChartGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → NormalDivisorChartAt M u d q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def NormalDoublePointsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → NormalDoublePointsOnDivisor M u q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorChartGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def NormalDivisorChartAtPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
    DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
    (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
    VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
    ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalModelDivisorChartGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ),
        M.ideal ⊔ Ideal.span {rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)} ≤ B ∧
        ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) < (d : ℕ) ∧
        ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0 →
          w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn B → NormalDivisorChartAtPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorGoodPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelDivisorGoodPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
  ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (h g a b : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (k : ℕ),
    c + (d + 1) = n + M.m ∧ (∀ j, f j ∈ M.ideal) ∧
    eval w h ≠ 0 ∧ (∀ p ∈ M.ideal, ∃ e : ℕ, h ^ e * p ∈ Ideal.span (Set.range f)) ∧
    eval w g = 0 ∧
    LinearIndependent ℂ (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
      Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) ∧
    0 < k ∧ eval w a ≠ 0 ∧ eval w b ≠ 0 ∧
    b * rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u) - a * g ^ k ∈ M.ideal ∧
    ∀ v : Fin n ⊕ Fin M.m → ℂ, (∀ i : Fin n, v (Sum.inl i) = 0) →
      ∑ s, eval w (pderiv s g) * v s = 0 → (∀ j, ∑ s, eval w (pderiv s (f j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamCritNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamCritNull.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) → IsOpen N →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W) →
      volume {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamDensIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamDensIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ)
    (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      Continuous f → tsupport f ⊆ N → (∀ i, SmoothNear (zeroSet W) (φ i)) →
        IntegrableOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w)
          (Metric.ball (0 : Fin d → ℂ) r)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamOffRegularZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamOffRegularZero.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), tsupport f ⊆ N →
      chartInt W A ((σ '' {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0})ᶜ.indicator f)
        φ = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamPieceInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamPieceInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (P : Set (Fin d → ℂ)),
      (∀ i, SmoothNear (zeroSet W) (φ i)) → MeasurableSet P → P ⊆ Metric.ball 0 r →
      (∀ w ∈ P, σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) →
      Set.InjOn (fun v => A *ᵥ σ v) P →
        chartInt W A ((σ '' P).indicator f) φ =
          ∫ w in P, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PosPartLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ),
    Measurable f → (∀ k, SmoothNear (zeroSet J) (φ k)) →
    (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧
        ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
            ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PosPartSplit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ))
    (y : Fin d → ℂ),
    IsFiniteProjection J A → Pairwise (Function.onFun Disjoint E) →
    (∀ x ∈ fibre J A y, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k) →
      ENNReal.ofReal (chartPosDens J A f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedIffRootFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormRootFull {σ : Type} [Fintype σ] {d N : ℕ} (X W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ) : Prop :=
  ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t = τ ∧
    ∀ s ∈ O, (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) ∈ X ∩ W ∧
      A (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = s ∧
      ℓ (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = r s

def PrimitiveFormSheetedIffRootFull.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
    (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 → ∀ W : Set (σ → ℂ), IsOpen W → z ∈ W →
      ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) ↔
        PrimitiveFormRootFull X W A ℓ δ q (A z) (ℓ z))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

