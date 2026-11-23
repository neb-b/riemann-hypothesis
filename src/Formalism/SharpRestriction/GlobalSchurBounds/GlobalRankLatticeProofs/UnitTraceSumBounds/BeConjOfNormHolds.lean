module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem l0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.l = 0 := by
  first
    | (unfold Formalism.MainNotions.GL3Theta.G1.l flog; simp)
    | (simp [Formalism.MainNotions.GL3Theta.G1.l, flog, PowerSeries.coeff_mk])
    | (show PowerSeries.coeff 0 (flog _ _) = 0; simp [flog])

theorem beConjOfNorm_holds : BeConjOfNorm := by
  intro p _ g S hOk hsw hadd hint hF hN hdec hph hbi
  exact conjugate_norm_bound p g.l g.ex g.ph (l0 g) hOk.2.2.1 hOk.2.2.2 (ph0 g) S hsw hadd hint hF hN hdec hph hbi

end Formalism.MainNotions.Ext.CutA
