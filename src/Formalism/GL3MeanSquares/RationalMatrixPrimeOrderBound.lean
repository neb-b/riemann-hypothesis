module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002

@[expose] public section

namespace Formalism.HermitianLattices.RamifiedHeckeModels

open Finset Matrix ComplexConjugate Formalism.HermitianLattices.LocalLatticeBases

def RationalMatrixPrimeOrderBound : Prop :=
  ∀ (n p : ℕ), p.Prime → ∀ A : Matrix (Fin n) (Fin n) ℚ, A ^ p = 1 → A ≠ 1 → p ≤ n + 1

def LemmaC_twist : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      (∀ s ∈ S, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R (S ⧸ (S.map ((ϖ ^ b) • U)).comap S.subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

def LemmaC_twist_ram : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

end Formalism.HermitianLattices.RamifiedHeckeModels
