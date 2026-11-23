module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.SqPosOfNe

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt

open CompanionTheory.PlacePermOperatorBicommutantSpan

theorem c_fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  fun _ _ _ _ _ _ h _ hφ => fou_sb h hφ

end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
