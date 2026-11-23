module

public import Mathlib
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LatticeTheta.Statement

@[expose] public section

-- bundled from Formalism.HermitianLattices.DefsCS
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def zmap {V W : Type*} [AddCommGroup V] [AddCommGroup W] {R : Type*} [Ring R] [Module R V]
    (ι : V →+ W) (M : Submodule R V) : Submodule ℤ W :=
  (M.toAddSubgroup.map ι).toIntSubmodule

def TraceReal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∃ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) ∧
      (∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖) ∧
      (∀ M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsFullLattice K M →
        ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))

def GenusCovol : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L → M ∈ genus h L →
    ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)]
      [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) = ZLattice.covolume (zmap ι L)

def ShortVectors : Prop :=
  ∀ (N : ℕ) (c C : ℝ), 0 < c → ∃ B : ℝ, ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ v ∈ Λ, v ≠ 0 → c ≤ ‖v‖) → ZLattice.covolume Λ ≤ C →
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ B

def GenusScale : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ d : ℕ, 0 < d ∧ ∀ M ∈ genus h L, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)

def FinIntermediate : Prop :=
  ∀ (W : Type) [AddCommGroup W] (P Q : AddSubgroup W), P ≤ Q → Finite (Q ⧸ P.addSubgroupOf Q) →
    Set.Finite {M : AddSubgroup W | P ≤ M ∧ M ≤ Q}

def IsomOfTrace : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V),
    (∀ x y : V, Algebra.trace ℚ K (h (g x) (g y)) = Algebra.trace ℚ K (h x y)) → g ∈ isom h

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.DualOrthSum
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def DualOrthSum : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (V₁ V₂ : Submodule K V), IsCompl V₁ V₂ →
    (∀ x ∈ V₁, ∀ y ∈ V₂, h x y = 0) → (∀ x ∈ V₂, ∀ y ∈ V₁, h x y = 0) →
    ∀ L₁ L₂ : Submodule R V, (L₁ : Set V) ⊆ V₁ → (L₂ : Set V) ⊆ V₂ →
      dual h (L₁ ⊔ L₂) = (dual h L₁ ⊓ V₁.restrictScalars R) ⊔ (dual h L₂ ⊓ V₂.restrictScalars R)

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.NeighbourConstruct
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def invIdeal (P : Ideal R) : Submodule R K :=
  ⨅ p ∈ P, (1 : Submodule R K).comap ((LinearMap.mulLeft R (algebraMap R K p)))

end Defs

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.StatementTheta
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V)
    (τ : ℂ) : ℂ :=
  ∑' x : L, Complex.exp (Real.pi * Complex.I * τ *
    ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))

end Defs

end Formalism.HermitianLatticesTheory
end
end

