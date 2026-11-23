module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.AddIntGTop
public import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HermLatFinMain
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.IsPositiveDefiniteMatrixCoefficientOfMemAlgA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermsSignSquared
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
section
theorem additive_integral_generation : PI.AddIntG.Target := PI.AddIntG.Wk.addIntG_top
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgWtDualUniq
section
theorem algebraic_weight_dual_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : Formalism.L2.Props.DualUnique L n :=
  PI.UnitaryGroupMassFormula.AlgWtDualUniq.main L n
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
section
theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExplicitFormula
section
theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermLatFin
section
theorem hermitian_lattice_finite : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula
section
theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert
section
theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
section
theorem phase_norm_units : PI.PhNormUnits.Target := PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_of_calculation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesInner
section
theorem fold_l2_bound_c (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesInner G μ :=
  PI.PoincareSeriesInner.W.fold_L2_complex_of PI.PoincareSeriesInner.W.complex_double_coset G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
section
theorem polynomial_coefficients : PI.PolyCoef := PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove
section
theorem quantum_minor_move : PI.QmMove := ⟨PI.UnitaryGroupMassFormula.QmMove.move_operator_vector, PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
section
theorem quantum_minor_row_expansion : PI.QmRowExp := PI.qmRowExp_of_rowForm quantum_minor_row_form
end

