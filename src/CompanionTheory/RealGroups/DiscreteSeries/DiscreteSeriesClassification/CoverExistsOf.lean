module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.DiscreteSeriesSU.GapInv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281

@[expose] public section

noncomputable section

namespace CompanionTheory.RgDs

open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.CoverDS GlobalTheory.Dec

theorem upqExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesUpqExists :=
  GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE

theorem exists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesExists :=
  GlobalTheory.Published.discreteSeriesExists_iff_upq.2 (upqExists_of hE)

theorem coverExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesCoverExists :=
  GlobalTheory.Published.CoverSeries.of_upq (upqExists_of hE) (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)

def ClassUsed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), GlobalTheory.DSId.IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        Formalism.MainNotions.S.IsDS ε lam σ → UEquiv ε σ π

theorem classUsed_of (hE : DSExists) (hK : KTypesAbove) (hI : DSInfChar) : ClassUsed := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ⟩ := hE n ε lam hl
  refine ⟨G, _, _, π, ⟨⟨hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2.1, hπ.2.2.2.2.1⟩, hI n ε lam G π hl hπ, ?_,
    hK n ε lam G π hl hπ⟩, fun H _ _ σ hσ => CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ⟩
  obtain ⟨S, hS⟩ := hπ.2.2.2.2.2.1
  exact ⟨S, hS, fun S' hS' => CompanionTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam G π hl hπ S' S hS' hS⟩

end CompanionTheory.RgDs
