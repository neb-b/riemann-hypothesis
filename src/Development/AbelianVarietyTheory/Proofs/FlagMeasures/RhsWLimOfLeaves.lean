module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation

@[expose] public section

noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves _root_.GlobalTheory.HaarDensChart.haarDens _root_.GlobalTheory.HyperboloidPolar.hypQ _root_.GlobalTheory.HypChartPf.hypChart _root_.GlobalTheory.GaugeKExists.gaugeK _root_.GlobalTheory.GaugeVolFixer.gaugeVolUk _root_.GlobalTheory.StabTube.tubeLimK _root_.GlobalTheory.HypOrbitUnique.orbRepY

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
