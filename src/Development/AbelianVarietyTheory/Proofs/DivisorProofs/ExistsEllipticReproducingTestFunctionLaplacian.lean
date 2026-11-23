module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySoluti

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section
namespace GlobalTheory.HCParam

section Local
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

end Local
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Degenerate
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end Degenerate
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Transpose
variable {E : Type} [Field E] [NumberField E] {a : ℕ} (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure]

end Transpose

end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

theorem reproduce : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) :=
  _root_.GlobalTheory.GLParametrix.exists_test_reproducing

end GlobalTheory.HCParam
