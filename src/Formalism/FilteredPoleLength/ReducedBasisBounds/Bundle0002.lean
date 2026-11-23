module

public import Mathlib
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

def IsLatticeSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ M : Submodule O V, Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O' K' V₁ (Submodule.span O' (j '' (M : Set V)))

def FinrankSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ V' : Submodule K V, finrank K' (Submodule.span K' (j '' (V' : Set V))) = finrank K V'

def SpanImageInf : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ (M : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Submodule.span O' (j '' (M : Set V)) ⊓
          (Submodule.span K' (j '' (V' : Set V))).restrictScalars O' =
        Submodule.span O' (j '' ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V))

def RelIndexSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ A B : Submodule O V, A.FG → B.FG →
      Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
      Formalism.LatticeIndexTer.idx O' V₁ (Submodule.span O' (j '' (A : Set V)))
                (Submodule.span O' (j '' (B : Set V))) =
        Formalism.LatticeIndexTer.idx O V A B

def LocalStepDescent : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O K V Θ → ∀ (d Y Z : ℝ) (e : ℕ),
      d * (Formalism.LatticeIndexTer.idx O' V₁
            (Submodule.span O' (j '' (M : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O')
            (Submodule.span O' (j '' (Θ : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O') : ℝ) ≤
          d * ((e : ℝ) * (finrank K' (Submodule.span K' (j '' (V' : Set V))) : ℝ) + Y) + Z →
        d * (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
          d * ((e : ℝ) * (finrank K V' : ℝ) + Y) + Z

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix

def ComplexHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (A : ℝ), (∀ i j, ‖M i j‖ ≤ A) →
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) ∧
      ‖M.det‖ ≤ (Real.sqrt n * A) ^ n

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Polynomial
open scoped ComplexOrder

def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)

def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

end Formalism.LatticeBaseChangeAlt
end
end

