module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def sat (Ω : Set (GA E N)) : Set (GA E N) := {g | ∃ γ ∈ latticeGL E N, γ * g ∈ Ω}

def SqIntAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ < ⊤

def PosNorm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 → 0 < ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ

end PositivityTheory.Rg.BcB.SpectralAccumulation.FD

end
