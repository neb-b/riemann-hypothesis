module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory

namespace UpperTheory.Lit.Cusp

variable {G : Type} [Group G] [TopologicalSpace G]

def conv [MeasurableSpace G] (μ : Measure G) (f h : G → ℂ) (x : G) : ℂ := ∫ g, f g * h (g⁻¹ * x) ∂μ

structure IsRay (N : Set G) (a : ℝ → G) (H : G → ℝ) : Prop where

  cont : Continuous a

  add : ∀ s t, a (s + t) = a s * a t

  norm : ∀ t, ∀ m ∈ N, (a t)⁻¹ * m * a t ∈ N

  contH : Continuous H

  inv : ∀ g, ∀ m ∈ N, H (g * m) = H g

  move : ∀ g t, H (g * a t) = H g + t

  bdd : ∀ D : Set G, IsCompact D → ∃ c : ℝ, ∀ g ∈ D, ∀ x, |H (g⁻¹ * x) - H x| ≤ c

  cpt : ∃ C : Set G, IsCompact C ∧ ∀ x, ∃ k ∈ C, ∀ t, ∃ m ∈ N, k * a t * k⁻¹ * x = x * a t * m

def IsEig (N : Set G) (a : ℝ → G) (s C : ℝ) (h : G → ℂ) : Prop :=
  Continuous h ∧ (∀ g, ‖h g‖ ≤ C) ∧ (∀ g, ∀ m ∈ N, h (g * m) = h g) ∧
    ∀ g t, h (g * a t) = Complex.exp ((s * t : ℝ) * Complex.I) * h g

def OpLe [MeasurableSpace G] (μ : Measure G) (N : Set G) (a : ℝ → G) (f : G → ℂ) (s r : ℝ) : Prop :=
  ∀ C h, IsEig N a s C h → ∀ x, ‖conv μ f h x‖ ≤ r * C

def Kills [MeasurableSpace G] (μ : Measure G) (N : Set G) (a : ℝ → G) (f : G → ℂ) : Prop :=
  ∀ s C h, IsEig N a s C h → ∀ x, conv μ f h x = 0

def IsBand (N : Set G) (H : G → ℝ) (h : G → ℂ) : Prop :=
  Continuous h ∧ (∃ C, ∀ g, ‖h g‖ ≤ C) ∧ (∀ g, ∀ m ∈ N, h (g * m) = h g) ∧ ∃ R : ℝ, ∀ g, h g ≠ 0 → |H g| ≤ R

end UpperTheory.Lit.Cusp

end
