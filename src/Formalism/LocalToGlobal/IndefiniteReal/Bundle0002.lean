module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
public import Formalism.HarderNarasimhan.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN

def CharFacts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
    (g : G), IsIntegral ℤ (charOf τ g) ∧
      ∀ σ : K →+* ℂ, σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧
        ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ)

def KeyZero : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V) (a : MonoidAlgebra K G),
    τ.asAlgebraHom a = 0 → eS τ ρ ∘ₗ ρ.asAlgebraHom a = 0

def Schur : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    (∀ s, eS (τ s) (τ s) = LinearMap.id) ∧ (∀ s t, s ≠ t → eS (τ s) (τ t) = 0) ∧
      ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K)

def DimSq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ s, finrank K (T s) ^ 2 ≤ Fintype.card G ∧
      ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), nS (τ s) H χ ^ 2 ≤ Fintype.card G

def IdemE : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
      (∀ s, eS (τ s) ρ ∘ₗ eS (τ s) ρ = eS (τ s) ρ) ∧
      (∀ s t, s ≠ t → eS (τ s) ρ ∘ₗ eS (τ t) ρ = 0)

def IdemP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ρ : Representation K G V),
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T),
      (∀ g : G, eS τ ρ ∘ₗ ρ g = ρ g ∘ₗ eS τ ρ) ∧
      (∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), eS τ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∘ₗ eS τ ρ) ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • eS τ ρ a ∈ A) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
      epP H χ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • epP H χ ρ a ∈ A

def CoreData {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
    {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {n : ℕ}
    (γ δ : Fin n → G) (c : Matrix (Fin n) (Fin n) K) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  c.det ≠ 0 ∧ (∀ i j, ((Γ i j : 𝓞 K) : K) = (Fintype.card G : K) ^ 2 * c i j) ∧
  (∀ i j (σ : K →+* ℂ), ‖σ (c i j)‖ ≤ (finrank K T : ℝ)) ∧
  ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    (∀ i j, ∀ a : V, epP H₀ χ₀ ρ (eS τ ρ a) = a →
      epP H₀ χ₀ ρ (ρ (δ i) (epP H χ ρ (ρ (γ j) a))) = c i j • a) ∧
    (∀ a : V, epP H χ ρ (eS τ ρ a) = a →
      ∑ j, ∑ i, c⁻¹ j i • epP H χ ρ (ρ (γ j) (epP H₀ χ₀ ρ (ρ (δ i) a))) = a)

def Core : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ → ∀ s,
      ∃ (γ δ : Fin (nS (τ s) H χ) → G) (c : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) K)
        (Γ : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) (𝓞 K)),
        CoreData (τ s) H₀ χ₀ H χ γ δ c Γ

def Metric : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [StarRing K]
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
    (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
      (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (eS τ ρ x) y = Formalism.HermitianLatticesTheory.majAt b X v x (eS τ ρ y)) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (v : InfinitePlace K),
      opNormAt b X b X v (epP H χ ρ ∘ₗ ρ g) ≤ 1

def LiftChar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (H : Type) [Group H] [Finite H] (χ : H →* Kˣ),
    ∃ χ' : H →* (𝓞 K)ˣ, ∀ h, (((χ' h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((χ h : Kˣ) : K)

def AllPartsTransfer : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [StarRing K] (G : Type) [Group G]
    [Fintype G] (S : Type) [Fintype S] (T : S → Type) [∀ s, AddCommGroup (T s)]
    [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
        (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
        (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
        ∀ A : Submodule (𝓞 K) V, IsGLat ρ A → TransferLatticeConditions τ H₀ χ₀ H χ b X ρ A

end Formalism.IndefR.LatticeTransfer
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.IndefiniteEpsilonOperator

structure Pair (G K : Type) [Group G] [Field K] where

  H : Subgroup G

  χ : H →* Kˣ

section Ops

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module K U]

def epOp [Finite G] (σ : Representation K G U) (P : Pair G K) : U →ₗ[K] U :=
  letI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ • ∑ h : P.H, ((P.χ h⁻¹ : Kˣ) : K) • σ (h : G)

def epSp [Finite G] (σ : Representation K G U) (P : Pair G K) : Submodule K U :=
  LinearMap.range (epOp σ P)

def nOf [Finite G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (P : Pair G K) : ℕ :=
  finrank K (epSp τ P)

end Ops

def la (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G)

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

end Lat

def M1 {K : Type} [Field K] {G : Type} [Group G] [Finite G] {S : Type} {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 : Pair G K) : Prop :=
  ∀ s, nOf (τ s) P0 = 1

end Formalism.IndefR.IndefiniteEpsilonOperator
end
end

