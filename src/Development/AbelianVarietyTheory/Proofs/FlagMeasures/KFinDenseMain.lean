module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPinsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357

@[expose] public section

namespace GlobalTheory.KFinDenseCarrier

theorem kFinDense_main : Formalism.L2.SG.Pf.CarrierXAll.KFinDense := by
  unfold Formalism.L2.SG.Pf.CarrierXAll.KFinDense
  exact GlobalTheory.KFinDenseDS.kFin_dense

instance : Fact (Formalism.L2.SG.Pf.CarrierXAll.KFinDense) := ⟨kFinDense_main⟩

end GlobalTheory.KFinDenseCarrier
