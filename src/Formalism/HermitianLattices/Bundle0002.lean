module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0001
public import Formalism.HermitianLattices.StatementLat
public import Formalism.GelfandTransference.Bundle0001

@[expose] public section

-- bundled from Formalism.HermitianLattices.GenusCovolBound
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def tdualSub {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (M : Submodule (NumberField.RingOfIntegers K) V) :
    Submodule (NumberField.RingOfIntegers K) V :=
  Submodule.span (NumberField.RingOfIntegers K)
    {y | ∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z}

def GenusCovolBound : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ C : ℝ, ∀ M ∈ genus h L, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C

def AutFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsFullLattice K L →
      Set.Finite {g : V ≃ₗ[K] V | g ∈ isom h ∧ gmap g L = L}

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.StatementMaj
section
open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

def vecAt (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def gramAt (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => v.embedding (h (b i) (b j))

def IsFrame (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K)
    (X : Matrix ι ι ℂ) : Prop :=
  IsUnit X.det ∧ ∃ ε : ι → ℂ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    X.conjTranspose * gramAt h b v * X = Matrix.diagonal ε

def fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecAt b v x)

def cnorm (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

def normAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ℝ :=
  cnorm (fcoord b X v x)

def majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : ℂ :=
  ∑ i, star (fcoord b X v x i) * fcoord b X v y i

theorem fcoord_add (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [vecAt, map_add (f := _)]

theorem fcoord_zero (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : fcoord b X v 0 = 0 := by
  have h0 : vecAt b v 0 = 0 := by
    funext i
    simp [vecAt]
  simp only [fcoord, h0, Matrix.mulVec_zero]

def realizeRaw (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun x p := if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re else (fcoord b X p.1 x p.2.1).im
  map_zero' := by
    funext p
    simp [fcoord_zero]
  map_add' := by
    intro x y
    funext p
    simp only [fcoord_add, Pi.add_apply]
    split_ifs <;> simp

def realize (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap.toAddMonoidHom.comp
    (realizeRaw b X)

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

def idealSmul (I : Submodule (RingOfIntegers K) K) (L : Submodule (RingOfIntegers K) V) :
    Submodule (RingOfIntegers K) V :=
  Submodule.span (RingOfIntegers K) {z | ∃ a ∈ I, ∃ x ∈ L, z = a • x}

def matAt (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) : Matrix ι ι ℂ :=
  (LinearMap.toMatrix b b g).map v.embedding

end Maj

end Formalism.HermitianLatticesTheory
end
end

