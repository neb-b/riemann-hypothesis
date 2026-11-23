module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

namespace UpperTheory.V.Z.Tf.GOne

def Temp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CG E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ∀ z ∈ B, ‖(z : ℂ)‖ = 1

def UnitOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsUnitary

def Thin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  (Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹) ∧
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w}.Infinite

end UpperTheory.V.Z.Tf.GOne

end
