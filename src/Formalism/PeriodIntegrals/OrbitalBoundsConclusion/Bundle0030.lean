module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
public import Formalism.PeriodIntegrals.EntAtD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UnitaryClassMass

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD
section
theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem in_s_class_constant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSFun D u u' :=
  fun _ Λ _ => PI.InSClassConstW.inSFun_all Λ _ _
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant
section
theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdSlopeLow
section
theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian
section
theorem unitary_class_mass_hermitian : PI.UJClassMass2.UJClassMass :=
  PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
end

