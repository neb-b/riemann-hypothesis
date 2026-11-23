module

public import Mathlib
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real Nat

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def nsq {κ : Type} [Fintype κ] (u : κ → ℂ) : ℝ := ∑ x, ‖u x‖ ^ 2

def mono {κ : Type} [Fintype κ] (u : κ → ℂ) (e : κ → ℕ) : ℂ := ∏ x, u x ^ e x

def mfact {κ : Type} [Fintype κ] (e : κ → ℕ) : ℕ := ∏ x, (e x)!

def cj {κ : Type} (u : κ → ℂ) : κ → ℂ := fun x => conj (u x)

def SupShift : Prop :=
  ∀ y e s : ℝ, 0 ≤ y → 0 < e → e < 1 → 0 ≤ s →
    s ^ y * Real.exp (-((1 - e) * s ^ 2) / 2) ≤ (1 - e) ^ (-(y / 2)) * Real.exp (ph y / 2)

def GaussCoord : Prop :=
  ∀ (κ : Type) [Fintype κ] (b : κ → ℝ), (∀ x, 0 < b x) →
    Integrable (fun u : κ → ℂ => Real.exp (-∑ x, b x * ‖u x‖ ^ 2)) ∧
    ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x

def FockJet : Prop :=
  ∀ (κ : Type) [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ) (S : ℝ),
    Continuous F → (∀ u, HasSum (fun e => c e * mono u e) (F u)) →
    (∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) →
    ∀ e : κ → ℕ,
      Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) ∧
      ∫ u : κ → ℂ, F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
        (π : ℂ) ^ Fintype.card κ * (c e * (mfact e : ℂ))

def BlockIntegral : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (R : (Pl × ι → ℂ) → W) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ u, ‖R u‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    ‖∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • R u‖ /
        π ^ (Fintype.card Pl * Fintype.card ι) ≤
      S * ∏ τ, (Real.exp (1 / 2) * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))

def BlockBound : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (c : (Pl × ι → ℕ) → ℂ) (Rc : (Pl × ι → ℕ) →₀ W)
    (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ, ∑ i, ν τ i = n τ) →
    (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    Continuous Th → (∀ u, HasSum (fun e => c e * mono u e) (Th u)) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ) →
    (∀ u, ‖Rc.sum (fun e A => mono (cj u) e • A)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    (∀ τ, 0 < Om τ) → (∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹) →
    ‖Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x, lam x.1 ^ e x) • A)‖ ^ 2 ≤
      S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ n τ *
        (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))))

end Formalism.DimensionVariation
