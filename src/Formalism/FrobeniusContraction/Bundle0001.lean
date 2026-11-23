module

public import Mathlib

@[expose] public section

-- bundled from Formalism.FrobeniusContraction.Statement
section
noncomputable section

namespace Formalism.WachCohomologyFacts

structure Base (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  ℓ : ℕ
  hℓ : ℓ.Prime
  X : A
  u : A
  c : A
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  hu : IsUnit u
  hc : IsUnit c
  comm : ∀ a, φ (γ a) = γ (φ a)
  γ_bij : Function.Bijective γ
  hφX : φ X = u * X * (X + (ℓ : A)) ^ (ℓ - 1)
  hγX : γ X - X = c * X * (X + (ℓ : A))
  γ_modX : ∀ a, γ a - a ∈ Ideal.span {X}

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

def Base.q (B : Base O A) : A := B.X + (B.ℓ : A)

def Base.p (B : Base O A) (s : ℕ) : A := (⇑B.φ)^[s] B.q

def Base.I (B : Base O A) : Ideal A := Ideal.span {B.X, (B.ℓ : A)}

structure Amb (B : Base O A) (AA : Type) [CommRing AA] [Algebra O AA] [Algebra A AA]
    [IsScalarTower O A AA] where
  φ : AA →ₐ[O] AA
  γ : AA →ₐ[O] AA
  φ_ext : ∀ a : A, φ (algebraMap A AA a) = algebraMap A AA (B.φ a)
  γ_ext : ∀ a : A, γ (algebraMap A AA a) = algebraMap A AA (B.γ a)
  comm : ∀ a, φ (γ a) = γ (φ a)
  γ_bij : Function.Bijective γ
  hq : IsUnit (algebraMap A AA B.q)
  hX : IsUnit (algebraMap A AA B.X)

variable {AA : Type} [CommRing AA] [Algebra O AA] [Algebra A AA] [IsScalarTower O A AA]

structure WachDatum {B : Base O A} (E : Amb B AA) (n : ℕ) (V : Type) [AddCommGroup V] [Module AA V]
    [Module A V] [IsScalarTower A AA V] [Module O V] [IsScalarTower O AA V] where
  N : ZMod n → Submodule A V
  φ : ZMod n → V →ₗ[O] V
  γ : ZMod n → V →ₗ[O] V
  φ_smul : ∀ i (a : AA) (x : V), φ i (a • x) = E.φ a • φ i x
  γ_smul : ∀ i (a : AA) (x : V), γ i (a • x) = E.γ a • γ i x
  comm : ∀ i x, φ i (γ i x) = γ (i + 1) (φ i x)
  γ_bij : ∀ i, Function.Bijective (γ i)
  γ_N : ∀ i x, x ∈ N i ↔ γ i x ∈ N i
  γ_sub : ∀ i, ∀ x ∈ N i, ∃ x' ∈ N i, γ i x - x = B.X • x'
  N_span : ∀ i, Submodule.span AA (N i : Set V) = ⊤
  φ_span : ∀ i, Submodule.span AA (Set.range (φ i)) = ⊤
  φ_N : ∀ i, ∀ x ∈ N i, ∃ k : ℕ, B.q ^ k • φ i x ∈ N (i + 1)
  N_φ : ∀ i, ∀ y ∈ N (i + 1), ∃ k : ℕ, B.q ^ k • y ∈ Submodule.span A (φ i '' (N i : Set V))

namespace WachDatum

variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]
variable (W : WachDatum E n V)

end WachDatum

section Hom

variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
variable {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]

structure Hom (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) where
  f : V₁ →ₗ[AA] V₂
  φ_comm : ∀ i x, f (W₁.φ i x) = W₂.φ i (f x)
  γ_comm : ∀ i x, f (W₁.γ i x) = W₂.γ i (f x)
  N_le : ∀ i, ∀ x ∈ W₁.N i, f x ∈ W₂.N i

namespace Hom

variable {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)

end Hom

end Hom

def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)

def LenBound : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g e : ℕ)
    (Z Bc I : Submodule O M) (s : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.WachCohomologyFacts
end
end

-- bundled from Formalism.FrobeniusContraction.StatementTop
section
noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.Top

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

end Formalism.WachCohomologyFacts.Top
end
end

