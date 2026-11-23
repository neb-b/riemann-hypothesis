module

public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubicExponentialFactor.ExpMvAddC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0004
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFactorIdentity.ExpMvEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.UnitaryScalars
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
section
theorem thetaCube_triple_relation : PI.CubicExponentialFactor.Lemma := PI.CubicExponentialFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockOneDeg
section
theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDualGen
section
theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue
section
theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocLatEq
section
theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OneCosetSharp
section
theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor
section
theorem phiCubeOfFactor : PI.PhiCubeOfFactor.Lemma := PI.PhiCubeOfFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
section
theorem product_formula_e : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
section
theorem quantum_minor_row_form : PI.QmRowForm :=
  PI.UnitaryGroupMassFormula.QmRowForm.qmRowForm_of PI.UnitaryGroupMassFormula.QmRowForm.double_row_decreasing PI.UnitaryGroupMassFormula.QmRowForm.double_row_increasing
    PI.UnitaryGroupMassFormula.QmRowForm.double_row_permutation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitDetRoot
section
theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin
section
theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin :=
  PI.UnitaryApproxFinWork.unitaryApproxFin_of PI.UnitaryApproxFinWork.topStep
    PI.UnitaryApproxFinWork.cayleyStep PI.UnitaryApproxFinWork.approxEStep
    PI.UnitaryApproxFinWork.weak_approximation_finite_unitary PI.UnitaryApproxFinWork.bounded_rational_unitary
    PI.UnitaryApproxFinWork.unitary_scalars PI.UnitaryApproxFinWork.eigenvalue_avoidance
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd
section
theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
end

