module

public import Mathlib

@[expose] public section

open Module

noncomputable section

namespace Formalism.PacketSums

def NoFixedSum : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N],
    (∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) →
    ∀ x y : G, ∑ n : N, LinearMap.trace ℂ V (τ (x * (n : G) * y)) = 0

def IwahoriNewton : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O), ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ (r : ℕ) (a : Fin r → ℕ), StrictAnti a →
    ∀ i₁ i₂ : Matrix (Fin r) (Fin r) O,
    (∀ i, IsUnit (i₁ i i)) → (∀ i, IsUnit (i₂ i i)) →
    (∀ i j, j < i → ϖ ∣ i₁ i j) → (∀ i j, j < i → ϖ ∣ i₂ i j) →
    ∀ k : ℕ, k ≤ r → ∃ u : Oˣ,
      (i₁ * Matrix.diagonal (fun i => ϖ ^ a i) * i₂).charpoly.coeff (r - k) =
        (u : O) * ϖ ^ (∑ j ∈ Finset.univ.filter (fun j : Fin r => r - k ≤ (j : ℕ)), a j)

def numK {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (μ : Fin r → ℤ)
    (β : Fin r → ℂ) : ℂ :=
  ∑ w : WK, ((Equiv.Perm.sign (w : Equiv.Perm (Fin r)) : ℤ) : ℂ) *
    ∏ i, β i ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i)

def vdm {r : ℕ} (β : Fin r → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (β i - β j)

def PacketSum : Prop :=
  ∀ (r : ℕ) (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (T : Finset (Equiv.Perm (Fin r))),
    Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin r)))⁻¹ * (p.1 : Equiv.Perm (Fin r))) →
    ∀ (μ : Fin r → ℤ) (α : Fin r → ℂ), (∀ i, α i ≠ 0) → Function.Injective α →
      ∑ y ∈ T, numK WK μ (fun i => α (y⁻¹ i)) / vdm (fun i => α (y⁻¹ i)) =
        (∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, α i ^ μ (w⁻¹ i)) / vdm α

def SignEven : Prop :=
  ∀ p q : ℕ, Odd (p + q) → (-1 : ℤ) ^ (p * q) = 1

end Formalism.PacketSums
