module

public import Formalism.SmithDeterminants.Bundle0001
public import Formalism.FockGram.StatementLat

@[expose] public section

-- bundled from Formalism.FockGram.StatementFock
section
open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)

end Formalism.E
end
end

-- bundled from Formalism.FockGram.StatementHerm
section
open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

def HermDual : Prop :=
  ∀ (S K V ι : Type) [CommRing S] [Field K] [StarRing K] [Algebra S K]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V] [Fintype ι] [DecidableEq ι]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V),
    Function.Injective (algebraMap S K) →
    (∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) →
    (Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K)) ∧
    ∀ [Module.Free ℤ S] [Module.Finite ℤ S] (GS : Matrix ι ι S),
      (∀ i j, B (b i) (b j) = algebraMap S K (GS i j)) → GS.det ≠ 0 →
      (Submodule.span S (Set.range b)).toAddSubgroup.relIndex
          (hdual B (Submodule.span S (Set.range b))).toAddSubgroup =
        (Algebra.norm ℤ GS.det).natAbs ∧
      (hdual B (Submodule.span S (Set.range b)) = Submodule.span S (Set.range b) ↔
        IsUnit GS.det)

end Formalism.E
end
end

