module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVol

@[expose] public section

namespace GlobalTheory.GaugeVolumeUD

theorem gaugeVolUD : PI.AprimeInfW.GaugeVolUD := fun k => Formalism.L2.SG.Pf.GV.gaugeVolU k

instance : Fact (PI.AprimeInfW.GaugeVolUD) := ⟨gaugeVolUD⟩

end GlobalTheory.GaugeVolumeUD
