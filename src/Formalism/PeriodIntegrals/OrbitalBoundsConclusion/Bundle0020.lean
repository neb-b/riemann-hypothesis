module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.FormalGroupChordFactor
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.MirabolicBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
public import Formalism.PeriodIntegrals.ScPiExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
section
theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
section
theorem fglChordFactor : PI.FglChordFactor.Lemma := PI.FglChordFactor.Wk.formal_group_chord_factor
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
section
theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
section
theorem mirabolic_bound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
section
theorem highest_weight_irreducible : PI.HwIrred :=
  PI.WHw.hwIrred_of PI.WHw.stable_subspace_closed PI.WHw.fixed_vectors_killed PI.WHw.highest_weight_in_closure
    PI.WHw.closure_eq_nabla
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnAdapted
section
theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage
section
theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiFrame
section
theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylLevelElementProperties
section
theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
end

