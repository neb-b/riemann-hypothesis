module

public import Mathlib
public import Formalism.HyperbolicPlaceProducts.Bundle0001
public import Formalism.FlagUnipotentLattices.Bundle0001
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

-- bundled from Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq
section
open Module NumberField nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def GramDetGen : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t t' : R),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -t else 0) W Z
        (Matrix.diagonal fun i => if i = Fin.last r then -t' else 0)).det =
      (-1) ^ (r + 1) *
        (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
          (W.submatrix Fin.castSucc Fin.castSucc).det)

def GramNondeg : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (B : V →ₗ[K] V →ₛₗ[σ] K) (v : ι → V),
    (Matrix.of fun i j => B (v i) (v j)).det ≠ 0 →
    LinearIndependent K v ∧
      finrank K (Submodule.span K (Set.range v)) = Fintype.card ι ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B x y = 0) → x = 0)

def DetIndexProductInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)

def DetIndexProductPlacesInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

-- bundled from Formalism.FlagUnipotentLattices.IdealCountLeW
section
noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def IotaDual : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : AddSubgroup U) (ι' : U → U),
    g ∈ O → star g = g → g ≠ 0 → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) → (∀ x ∈ L₀', ι' x ∈ L₀) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
      (∀ l' ∈ L₀', ∀ x ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' x - x = g • l) → h (g⁻¹ • (l' - ι' l')) x ∈ O) ∧
      (∀ l' ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' l' - l' = g • l) → g⁻¹ • (l' - ι' l') ∈ L₀)

def hdual {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (M : AddSubgroup U) : AddSubgroup U where
  carrier := {x | ∀ y ∈ M, h x y ∈ O}
  add_mem' := by
    intro a b ha hb y hy
    simpa using O.add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    simp
  neg_mem' := by
    intro a ha y hy
    simpa using O.neg_mem (ha y hy)

def DualIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [FiniteDimensional E U] (h : U →ₗ[E] U →ₗ⋆[E] E)
    (M N : Submodule (𝓞 E) U), (∀ x : U, (∀ y : U, h x y = 0) → x = 0) → N ≤ M → M.FG →
    Submodule.span E (N : Set U) = ⊤ →
      (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup

end Formalism.HermitianLatticeCounting.S6
end
end

