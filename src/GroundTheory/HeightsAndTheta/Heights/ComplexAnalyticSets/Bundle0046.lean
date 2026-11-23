module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermCanonicalCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimeGermCanonicalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (δ : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ δ (A w) ∧
      (¬ ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) = ∑ i, h i z * p i z) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
          (∀ j, AnalyticAt ℂ (a j) (A w)) ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = ∑ i, h i z * p i z) ∧
      ∀ W ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        ∃ x : Fin N → σ → ℂ, (∀ j, x j ∈ W ∧ (∀ i, p i (x j) = 0) ∧ A (x j) = y) ∧
          Function.Injective fun j => ℓ (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsGermCombination {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ)
    (f : (σ → ℂ) → ℂ) : Prop :=
  ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, f z = ∑ i, h i z * p i z

noncomputable def monicOfCoeffs {N : ℕ} (c : Fin N → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

def IsPrimitivePresentation {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) {N : ℕ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) : Prop :=
  (∀ j, AnalyticAt ℂ (c j) (A w)) ∧ AnalyticAt ℂ δ (A w) ∧
  IsGermCombination w p (fun z => ℓ z ^ N + ∑ j, c j (A z) * ℓ z ^ (j : ℕ)) ∧
  (∀ a : Fin N → (Fin d → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) (A w)) →
    IsGermCombination w p (fun z => ∑ j, a j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ j, ∀ᶠ y in 𝓝 (A w), a j y = 0) ∧
  (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → (monicOfCoeffs fun j => c j y).Separable) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) ∧
      IsGermCombination w p (fun z => δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ))) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
      ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n)

def PrimeGermPrimitivePresentation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ)
      (c : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ),
      IsPrimitivePresentation w p A ℓ c δ ∧ ¬ IsGermCombination w p (fun z => δ (A z))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ M ∈ 𝓝 w, ∀ y ∈ X ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def ProjectionInjectiveOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 →
      ∃ W : Set (σ → ℂ), IsOpen W ∧ z ∈ W ∧
        ∃ A : (σ → ℂ) →L[ℂ] (Fin k → ℂ), Set.InjOn A (zeroSetIn I ∩ W)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n d : ℕ}

def IsSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ A *ᵥ x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (A *ᵥ x) = x ∧
    (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, A *ᵥ x' ∈ U → x' = s (A *ᵥ x')


open scoped Classical in
open Classical in
def sheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ fibre J A y),
    if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0

def chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y

def chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y

def chartInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ y, chartDens J A f φ y


open scoped Classical in
open Classical in
def varInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A then chartInt J h.choose f φ else 0

def SmoothNear (S : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ φ U

def linEval (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def euclPot (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def energyInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (B : Set (Fin n → ℂ)) (χ : (Fin n → ℂ) → ℝ) : ℝ :=
  chartInt J A (B.indicator fun _ => 1) (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) -
    chartInt J A (B.indicator χ) (vecCons χ fun _ => euclPot)

structure VarBranch (J : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (p : Fin n → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin k → ℂ) → Fin n → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  injOn : Set.InjOn toFun (Metric.ball 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.ball 0 radius) (zeroSet J)

def VarBranch.image {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J k p) : Set (Fin n → ℂ) :=
  b.toFun '' Metric.ball 0 b.radius

def VarBranch.slice {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J (k + 1) p) : Set (Fin n → ℂ) :=
  b.toFun '' (Metric.ball 0 b.radius ∩ {t | t 0 = 0})

def VanishesToOrder {k : ℕ} (F : (Fin (k + 1) → ℂ) → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  ∃ H : (Fin (k + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 r) ∧
    (∀ t ∈ Metric.ball 0 r, H t ≠ 0) ∧ ∀ t ∈ Metric.ball 0 r, F t = t 0 ^ m * H t

def IntegralIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → Integrable (chartAbsDens J A f φ) →
      Integrable (chartAbsDens J A' f φ) ∧ chartInt J A f φ = chartInt J A' f φ

def PointIntegral.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin 0 → (Fin n → ℂ) → ℝ),
    varInt (RingHom.ker (MvPolynomial.eval p)) 0 f φ = f p

def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
        (∀ R : ℝ, Tendsto (fun k => energyInt J A (Metric.closedBall 0 R) (χ k)) atTop (𝓝 0)) ∧
        (∀ (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), (∀ i, SmoothNear (zeroSet J) (φ i)) →
          Tendsto (fun k => ∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (χ k) φ) y) atTop (𝓝 0))

def StokesOnVariety.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → (HasCompactSupport f ∨ HasCompactSupport g) →
      varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ)

def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Integrable (chartAbsDens J A
        ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖) φ)

def LocalOrder.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      localMult (J ⊔ Ideal.span {linForm u}) W = ∑ b, ord b

section Inhabitants

theorem linForm_single {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : ℂ)) = X i := by
  classical
  simp [linForm, Pi.single_apply]

theorem space_dim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin n) ℂ))) = (n : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem smoothNear_of_contDiff {n : ℕ} {S : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ}
    (h : ContDiff ℝ ∞ φ) : SmoothNear S φ :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, h.contDiffOn⟩

theorem contDiff_euclPot (n : ℕ) : ContDiff ℝ ∞ (euclPot : (Fin n → ℂ) → ℝ) := by
  unfold euclPot
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) j)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

