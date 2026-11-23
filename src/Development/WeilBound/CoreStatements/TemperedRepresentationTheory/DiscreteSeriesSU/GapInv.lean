module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneFock
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod

@[expose] public section

namespace PositivityTheory.DiscreteSeriesGap.GapInv

theorem dsUnique_dec : GlobalTheory.Dec.DSUnique := by
  intro n ε lam H _ _ σ H' _ _ σ' hlam hσ hσ'
  exact GlobalTheory.CompanionTheory.DSUniq.ds_unique
    CompanionTheory.D.LK.hMultAlg CompanionTheory.D.LK.hKModExists
    CompanionTheory.D.LK.hOrthCyc n ε lam H H' σ σ' hlam hσ hσ'

theorem lowKMultOne_dec : GlobalTheory.Dec.LowKMultOne := CompanionTheory.D.LK.low_K_type_multiplicity_one

end PositivityTheory.DiscreteSeriesGap.GapInv
