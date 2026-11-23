module

public import Mathlib

@[expose] public section

-- bundled from Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality
section
open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements

def AutCount : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ) (v : Fin e → M),
    Submodule.span R (Set.range v) = ⊤ → Nat.card (M ≃ₗ[R] M) ≤ Nat.card M ^ e

end Formalism.SLP.GlobalBoundRefinements
end
end

-- bundled from Formalism.HyperbolicPlaceProducts.Statement
section
open Module

noncomputable section

namespace Formalism.SLP

def TorsionIndexEq : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ),
    Nat.card A = Nat.card (nsmulAddMonoidHom g : A →+ A).range *
      Nat.card (nsmulAddMonoidHom g : A →+ A).ker

def TorsionIndex : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ) (K : AddSubgroup A),
    (∀ x ∈ K, g • x = 0) →
    Nat.card (nsmulAddMonoidHom g : A →+ A).range * Nat.card K ≤ Nat.card A

section Place

variable {𝕜 : Type*} [RCLike 𝕜]
  {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']

def herm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (x y : V) : 𝕜 :=
  inner 𝕜 y x

def Ph (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') : Submodule 𝕜 W :=
  (LinearMap.ker (φ₁.toLinearMap.comp (Submodule.inclusion (inf_le_left : D₁ ⊓ D₂ ≤ D₁)) -
      φ₂.toLinearMap.comp (Submodule.inclusion (inf_le_right : D₁ ⊓ D₂ ≤ D₂)))).map
    (D₁ ⊓ D₂).subtype

def bb (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂) :
    𝕜 :=
  herm (x₁ : W) (x₂ : W) - herm (φ₁ x₁) (φ₂ x₂)

end Place

def BBBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂),
    ‖bb D₁ D₂ φ₁ φ₂ x₁ x₂‖ ≤
      2 * ‖(Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₁ : W)‖ *
        ‖(Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₂ : W)‖

def SesqDet : Prop :=
  ∀ (V₁ V₂ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ), (∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) →
    ∀ (m : ℕ) (u : Fin m → V₁) (w : Fin m → V₂),
      ‖(Matrix.of fun i j => B (u i) (w j)).det‖ ^ 2 ≤
        c ^ (2 * m) * ‖(Matrix.gram ℂ u).det‖ * ‖(Matrix.gram ℂ w).det‖

def SubmoduleCountDed : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Finite M] (e : ℕ) (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    Nat.card (Submodule R M) ≤ Nat.card M ^ e

def SubmoduleIndexCountO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (j : ℕ), 1 ≤ j →
    {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.Finite ∧
      {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard ≤
        finrank ℚ E ^ (Nat.primeFactorsList j).length *
          j ^ finrank (NumberField.RingOfIntegers E) M

def OmegaPow : Prop :=
  ∀ n j : ℕ, 1 ≤ n → 1 ≤ j →
    (n : ℝ) ^ (Nat.primeFactorsList j).length ≤ (j : ℝ) ^ Real.logb 2 n

end Formalism.SLP
end
end

