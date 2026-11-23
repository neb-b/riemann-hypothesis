module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace PositivityTheory.Affgl.CT

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

def ct [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (φ : GA E a → ℂ) : GA E a → ℂ :=
  fun g => ∫ x in 𝓕, φ (unip x * g) ∂μ

end PositivityTheory.Affgl.CT

end
