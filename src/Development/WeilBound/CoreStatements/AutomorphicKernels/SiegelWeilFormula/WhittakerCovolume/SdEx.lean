module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdeles
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.KWhit

theorem sdEx : SdEx := by
  intro F E _ _ _ _ _ σ hcm M J hJ ψ hψ n
  exact ⟨_root_.GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples F E σ hcm M J hJ ψ hψ n, _root_.GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm F E σ hcm ψ hψ n⟩

end PositivityTheory.SiegelWeilFormula.KWhit
