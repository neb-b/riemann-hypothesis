module

public import Mathlib

@[expose] public section

open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def sgram {R M ι : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) (v : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => B (v i) (v j)

def orthSum {R M₁ M₂ : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) :
    (M₁ × M₂) →ₗ⋆[R] (M₁ × M₂) →ₗ[R] R :=
  (B₁.comp (LinearMap.fst R M₁ M₂)).compl₂ (LinearMap.fst R M₁ M₂) +
    (B₂.comp (LinearMap.snd R M₁ M₂)).compl₂ (LinearMap.snd R M₁ M₂)

def SubIndexNorm : Prop :=
  ∀ (S M ι : Type) [CommRing S] [AddCommGroup M] [Module S M]
    [Module.Free ℤ S] [Module.Finite ℤ S] [Fintype ι] [DecidableEq ι]
    (b : Basis ι S M) (N : Submodule S M) (bN : Basis ι S N),
    Nat.card (M ⧸ N) = (Algebra.norm ℤ (b.det fun i => (bN i : M))).natAbs

def CovolGram : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E),
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = Real.sqrt (Matrix.gram ℝ b).det

end Formalism.E
