module

public import Mathlib
public import Development.WeilBound.CoreStatements.ResolutionCharZero.Bundle0001
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroBotOfEff

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
section
namespace PositivityTheory.ResPlug.FromRes

theorem resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  PositivityTheory.ResPlug.resK_of_weak resW princW

end PositivityTheory.ResPlug.FromRes
end

-- bundled from Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup

theorem principalisationCharZero_of_boundary (hB : GBoundary) : PrincipalisationCharZero :=
  principalisationCharZero_of_eff hB PositivityTheory.ResPlug.GEndGen.gEff

theorem principalisationCharZero_bot_closed :
    ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
      SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
      ∀ (I : X.IdealSheafData), (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
        ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
          IsSncBlowupSeq g ⊥ s E' ∧ Smooth (s ≫ g) ∧
          FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
          IsIso (s ∣_ I.support.compl) :=
  principalisationCharZero_bot_of_eff PositivityTheory.ResPlug.GEndGen.gEff

end PositivityTheory.ResPlug.WeightsCompactStabilizer
end
end

