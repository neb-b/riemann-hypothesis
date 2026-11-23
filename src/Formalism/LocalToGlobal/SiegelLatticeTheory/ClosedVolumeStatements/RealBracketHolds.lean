module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AprimeInf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem AprimeInf_holds [hG : Fact PI.AprimeInfW.GaugeVolUD] : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  PI.AprimeInfAsm.aprime_infinite_real Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds hG.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem JacGauge_holds : Formalism.L2.SG.Pf.JacGauge := Formalism.L2.SG.Pf.jacGauge

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_holds (hC : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  Formalism.L2.SG.Pf.NcReal.JX.realBracket_of_jac JacGauge_holds hC AprimeInf_holds
    (fun n ε => Formalism.MainNotions.S.Gauge.gauge_density_exists n ε)

end Formalism.L2.SG.Closed
