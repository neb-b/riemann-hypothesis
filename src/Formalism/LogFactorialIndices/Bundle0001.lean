module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LogFactorialIndices.StatementIdx
section
noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

section Defs

variable (O K X : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup X] [Module K X]
  [Module O X]

def IsLat (A : Submodule O X) : Prop := A.FG ∧ Submodule.span K (A : Set X) = ⊤

end Defs

section Defs2

variable (O X : Type) [CommRing O] [AddCommGroup X] [Module O X]

def qlen (A B : Submodule O X) : ℕ∞ := Module.length O (A ⧸ B.comap A.subtype)

def idx (A B : Submodule O X) : ℤ := ((qlen O X A B).toNat : ℤ) - ((qlen O X B A).toNat : ℤ)

end Defs2

def LatFinite : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B : Submodule O X), IsLat O K X A → IsLat O K X B → qlen O X A B ≠ ⊤

def LatBasis : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (A : Submodule O X), IsLat O K X A →
      ∃ b : Basis (Fin (finrank K X)) K X, A = Submodule.span O (Set.range b)

def IdxAdd : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B C : Submodule O X), IsLat O K X A → IsLat O K X B → IsLat O K X C →
      idx O X A C = idx O X A B + idx O X B C

def IdxDet : Prop :=
  ∀ (O K X Y ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b →
      idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ)

def IdxScale : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ → ∀ (s : ℤ) (N : Submodule O X), IsLat O K X N →
      idx O X N (N.map ((((algebraMap O K ϖ) ^ (-s)) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
        -s * (finrank K X : ℤ)

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.StatementNorm
section
noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate

def LogProductFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (x : L), x ≠ 0 →
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ =
      ∑ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        (FractionalIdeal.count L 𝔭
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) x) : ℝ) *
          Real.log (Ideal.absNorm 𝔭.asIdeal : ℝ)

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.StatementSize
section
noncomputable section

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def PhIncr : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 ≤ u ∨ 1 ≤ v) → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

end Formalism.LatticeIndexTer
end
end

