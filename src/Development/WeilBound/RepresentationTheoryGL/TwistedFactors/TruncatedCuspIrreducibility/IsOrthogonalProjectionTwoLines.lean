module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay

@[expose] public section

noncomputable section

open MeasureTheory NumberField Set
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core
open scoped ENNReal NumberField.AdeleRing InnerProductSpace

namespace PositivityTheory.Rg.Tf.Adel

open PositivityTheory.Rg.Tf.IntegralApplyAeEq

variable {K : Type} [Field K] [NumberField K]

abbrev Eu (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

structure Line (μ : Measure (G1 K (2 + 2))) {μ₂ : Measure (G1 K 2)} (τ₁ τ₂ : Submodule ℂ (L2 μ₂))
    (D : TypeDat K (2 + 2)) (d : ℕ) where
  sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)
  inj : Function.Injective sec
  onto : ∀ f, f ∈ LinearMap.range sec ↔ IsSec τ₁ τ₂ f ∧ D.Fix f
  J : L (Eu d) →ₗᵢ[ℂ] L2 μ
  spec : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) →
    Reps μ (J u) (theta β (sec v))

def flat (z : ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) : ℂ := Complex.exp ((z + 2) * (HP 2 2 x : ℂ)) * f x

def IsOrthogonalProjectionTwoLines {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint P ∧ P ∘L P = P ∧ ∀ h, P h = 0 ↔ (∀ u, ⟪J u, h⟫_ℂ = 0) ∧ ∀ v, ⟪J' v, h⟫_ℂ = 0

def Stable {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (D : TypeDat K n) (θ : Twist μ) : Prop :=
  (∀ k, θ.e k ∈ D.U ↔ k ∈ D.U) ∧ ∀ k ∈ D.U, D.e (θ.e k) = D.e k

structure Pair (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) : Prop where
  irr₁ : CuspIrr μ₂ τ₁
  irr₂ : CuspIrr μ₂ τ₂
  orth : τ₁ ⟂ τ₂

def LineEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ D : TypeDat K (2 + 2), ∃ d, Nonempty (Line μ τ₁ τ₂ D d)

section Steps

variable (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
  {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')

def ShiftCausal (T₀ : ℝ) : Prop :=
  (∀ (t : ℝ) (u u' : L (Eu d)) (v v' : L (Eu d')), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
    ⟪A.J u', A'.J v⟫_ℂ = ⟪A.J u, A'.J v'⟫_ℂ) ∧
  ∀ (s : ℝ) (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * T₀ - s → v x = 0) →
    ⟪A.J u, A'.J v⟫_ℂ = 0

def ActsBy (f : CC K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d) : Prop :=
  Ker β ∧ Conv A.J A.J (Rop μ f) β ∧
    ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)), ∫ g, f g * flat z (A.sec v) (x * g) ∂μ = flat z (A.sec (symb β z v)) x

def Family (T₀ : ℝ) (P : L2 μ →L[ℂ] L2 μ) (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (C : ℝ) : Prop :=
  (∀ (f : CC K (2 + 2)) β β', ActsBy μ A f β → ActsBy μ A' f β' → ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
  ∀ (X Λ : L2 μ →L[ℂ] L2 μ) (κ : ℝ → Eu d →L[ℂ] Eu d') (T B : ℝ), Ker κ → Conv A.J A'.J X κ → X ∘L P = P ∘L X → T₀ ≤ T →
    IsTrunc A.J A'.J T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ B / (1 + |z.im|)) →
    ‖trace (Λ ∘L X ∘L P ∘L Λ) -
        (1 / 2 : ℂ) * LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ (symb κ 0 : Eu d →ₗ[ℂ] Eu d'))‖ ≤
      C * B * Real.exp (-2 * T)

end Steps

end PositivityTheory.Rg.Tf.Adel
