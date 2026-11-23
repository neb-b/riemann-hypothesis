module

public import Mathlib

@[expose] public section

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

abbrev dual (Λ : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) Λ


variable (V) in
def DualIsLattice [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    DiscreteTopology (dual Λ) ∧ ∀ [DiscreteTopology (dual Λ)], IsZLattice ℝ (dual Λ)


variable (V) in
def CovolumeDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (dual Λ)] [IsZLattice ℝ (dual Λ)],
    ZLattice.covolume (dual Λ) = (ZLattice.covolume Λ)⁻¹


variable (V) in
def DualDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ], dual (dual Λ) = Λ


variable (V) in
def PoissonDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b →
    f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    (𝓕 f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    ∀ x : V,
      Summable (fun μ : dual Λ =>
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))


variable (V) in
def PoissonSchwartz [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : 𝓢(V, ℂ)) (x : V),
      Summable (fun μ : dual Λ =>
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))

end Formalism.H
