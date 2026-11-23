module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

namespace Line

end Line

section FS


end FS

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure WeightReg (ι : K → Type) [∀ k, Fintype (ι k)] where

  reg : ℝ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  deg : ∀ t A, (reg t A).a = A.a
  smooth : ∀ t A, IsSmoothHerm A → IsSmoothHerm (reg t A)
  shift : ∀ t (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : ℝ), 0 < k → A'.a = A.a →
    (∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → A'.h z = k * A.h z) →
    ∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → (reg t A').h z = k * (reg t A).h z


open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in
def weightRegRef : WeightReg (PBlk 2) where
  reg _ A := (HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).tensor
    (constLine (A.h (fun _ => 1) / (HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).h (fun _ => 1))
      (div_pos (A.pos _ fun _ => ⟨0, one_ne_zero⟩)
        ((HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).pos _ fun _ => ⟨0, one_ne_zero⟩)))
  deg _ A := by simp [HermLine.tensor, constLine, HermLine.ofMetrics]
  smooth _ A _ := isSmoothHerm_tensor (Inter.isSmoothHerm_ofMetrics_fs _) (isSmoothHerm_constLine _ _)
  shift _ A A' k hk ha hh z _ := by
    have h1 := hh (fun _ => 1) fun _ => ⟨0, one_ne_zero⟩
    simp only [HermLine.tensor, constLine, ha, h1]
    ring

end Reg

section Heights

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

end Heights

end GroundTheory.Heights₂.Heights.LowerBoundFree
