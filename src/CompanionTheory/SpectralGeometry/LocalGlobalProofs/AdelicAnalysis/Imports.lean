module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianFormStatement

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem siegelWeilUnitaryConvergent : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent :=
  fun F E _ _ _ _ _ σ hσ M J hJ =>
    ⟨finVol_unitaryGroup F E σ hσ M J hJ, GlobalTheory.T.siegel_densities_of_hermitian_form F E σ hσ M J hJ⟩

end GlobalTheory.CompanionTheory.SW
