module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.CorankShareLayerCake.FR

open Finset Module LinearMap

def hs2 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F) : ℝ :=
  (LinearMap.trace ℂ E (LinearMap.adjoint A ∘ₗ A)).re

def frK {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ℝ) (B : V →ₗ[ℂ] H) : V →ₗ[ℂ] V :=
  (c : ℂ) • (LinearMap.adjoint B ∘ₗ B)

def frQ {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ∑ i, (c i : ℂ) • (B i ∘ₗ LinearMap.adjoint (B i))

def LayerCake : Prop :=
  ∀ (D : ℕ) (x : Fin D → ℝ) (a HH : ℝ) (w : ℝ → ℝ), 0 < D → 0 ≤ HH →
    (∀ j, a - HH ≤ x j) →
    IntervalIntegrable (fun τ => min 1 (w τ)) MeasureTheory.volume 0 HH →
    (∀ τ ∈ Set.Icc (0 : ℝ) HH, ((univ.filter (fun j => x j < a - τ)).card : ℝ) ≤ w τ * D) →
    a - (∫ τ in (0 : ℝ)..HH, min 1 (w τ)) ≤ (∑ j, x j) / D

end Formalism.CorankShareLayerCake.FR
