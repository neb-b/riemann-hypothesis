module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IsCentredDiscCover {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ)
    (ρ : ℝ) (N : ℕ) : Prop :=
  w ∈ Y ∧ 0 < N ∧ Set.MapsTo p Y (ball (p w) ρ) ∧ (∀ x ∈ Y, p x = p w → x = w) ∧
    (∀ t ∈ ball (p w) ρ, t ≠ p w → {x | x ∈ Y ∧ p x = t}.encard = N) ∧
    (∀ K ⊆ ball (p w) ρ, IsCompact K → IsCompact {x | x ∈ Y ∧ p x ∈ K}) ∧
    (∀ x ∈ Y, p x ≠ p w → ∃ (O : Set ℂ) (V : Set (σ → ℂ)) (g : ℂ → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
      DifferentiableOn ℂ g O ∧ (∀ t ∈ O, p (g t) = t) ∧ Y ∩ V = g '' O)

def CentredDiscCoverCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ),
    IsCentredDiscCover Y w p ρ N →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChangeOfVariablesDegree
section
set_option maxSynthPendingDepth 1

open scoped ContDiff

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def ChangeOfVariablesDegree.Statement : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → Fin n → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport (fun x => φ x - x) →
      ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ x, f (φ x) * (fderiv ℝ φ x).det = ∫ x, f x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCircleArgumentPrinciple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

def CircleArgumentPrinciple.Statement : Prop :=
  ∀ (h : ℂ → ℂ) (O : Set ℂ) (c : ℂ) (r : ℝ),
    0 < r → IsOpen O → closedBall c r ⊆ O → DifferentiableOn ℂ h O → (∀ s ∈ sphere c r, h s ≠ 0) →
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) ∧
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ O →
        (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv h s / h s) = (Z.map φ).sum

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompactHolomorphicFibreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def CompactHolomorphicFibreFinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (y : Fin m → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → IsCompact {v | v ∈ U ∧ f v = y} →
      {v | v ∈ U ∧ f v = y}.Finite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalFlatNotInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CriticalFlatNotInjective.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (a : Fin k → ℂ),
    2 ≤ k → IsOpen U → DifferentiableOn ℂ f U → a ∈ U →
    LinearMap.det (fderiv ℂ f a : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
    (∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 → fderiv ℂ f b = 0) →
    ¬ Set.InjOn f U

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory

noncomputable section

def CriticalImageNull.Statement : Prop :=
  ∀ (d n : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → Fin n → ℂ), IsOpen U →
    DifferentiableOn ℂ f U →
      μH[((2 * d : ℕ) : ℝ)] (f '' {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)}) = 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StExtensionQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ExtensionQuotientLength.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (r : R),
    Function.Injective (algebraMap R B) → algebraMap R B r ∈ nonZeroDivisors B →
    Module.length R (B ⧸ LinearMap.range (Algebra.linearMap R B)) ≠ ⊤ →
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R (B ⧸ Ideal.span {algebraMap R B r})

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteCoverPuncturedPolydisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

def FiniteCoverPuncturedPolydisc.Statement : Prop :=
  ∀ (e N : ℕ) (c : Fin (e + 1) → ℂ) (r : ℝ) (Y : Type) [TopologicalSpace Y]
    (p : Y → ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})),
    0 < r → c 0 = 0 → IsCoveringMap p → (∀ z, (p ⁻¹' {z}).encard = N) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (δ : ℝ)
      (ψ : Fin m → ↥(Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧ (∀ b, Continuous (ψ b)) ∧
      (∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) =
        Function.update (t : Fin (e + 1) → ℂ) 0 ((t : Fin (e + 1) → ℂ) 0 ^ ord b)) ∧
      (∀ b, Function.Injective (ψ b)) ∧
      (∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t') ∧
      (∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < δ ^ N → ∃ b t, ψ b t = y)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsFiniteModuloOver {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) {k : ℕ}
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) : Prop :=
  ∃ (n : ℕ) (e : Fin n → (σ → ℂ) → ℂ), (∀ m, AnalyticAt ℂ (e m) x) ∧
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (b : Fin n → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ m, AnalyticAt ℂ (b m) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z = ∑ m, b m (L z) * e m z + ∑ i, h i z * f i z

def FiniteModuloIntegral.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (L z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatDimFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatDimFormula.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))

def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGeneralProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix

noncomputable section

def GeneralProjection.Statement : Prop :=
  ∀ (n d m : ℕ) (L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)), (∀ b, Function.Injective (L b)) →
    ∃ π : Matrix (Fin d) (Fin n) ℂ, ∀ b, Function.Injective fun v => π *ᵥ L b v

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

