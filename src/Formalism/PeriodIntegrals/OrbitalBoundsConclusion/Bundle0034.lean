module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.BetaModXOfIota
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.Bundle0025
public import Formalism.PeriodIntegrals.NormRepChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaModX
section
theorem beta_mod_iota_surjective (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaL D u u' :=
  PI.UnitaryGroupMassFormula.BetaModX.betaModX_of_iota PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_surjective_holds D u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormRepChange
section
noncomputable section

open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_representative_move (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (hS : Formalism.L2.SG.TermDef.TermStable D u u') (hE : Formalism.L2.SG.TermDef.TermEqIff D u u') (hF : Formalism.L2.SG.TermDef.TermFun D u u') (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hsig : (Formalism.MainNotions.S.VS D).SigOK) : PI.NormRepChange.NormRepMove D u u' :=
  PI.NRCW.normRepMove_of_steps D u u' hE (PI.NRCW.stepExp D) (PI.NRCW.stepGram D) (PI.NRCW.stepGlob D)
    (PI.NRCW.stepLoc D) (PI.NRCW.stepTr D)
end
end

