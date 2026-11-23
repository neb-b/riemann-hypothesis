module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral
public import Formalism.PeriodIntegrals.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS
section
theorem term_id_iff_in_s (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermIdIffInS D u u' :=
  PI.UnitaryGroupMassFormula.IdCellInSW.termIdIffInS_of D (PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D) u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer
section
theorem infinite_measure_transfer : Formalism.L2.SG.Pf.MeasInf.InfTransfer :=
  Formalism.L2.SG.Pf.MeasInfW.measInfXfer_of Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_recursion Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_closed_form Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_closed_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddUp
section
theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr
section
theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
end

