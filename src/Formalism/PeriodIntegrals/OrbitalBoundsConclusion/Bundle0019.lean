module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyFin
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.IntertwinerRankLeOne
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.FrameC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Transf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.HSBlocksMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft
public import Formalism.PeriodIntegrals.ScPiExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.InnerOfNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Weights
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Formula

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockJointMult
section
theorem fock_joint_multiplicity : PI.FockDegreeTwoParts.JointMult := PI.FJM.fockJointMult_of_cauchy PI.FJM.cauchy_highest_weight
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar
section
theorem convolution_scalar : Formalism.L2.SG.GGMirabolic.ConvScalarOfLit :=
  PI.GGConvScalarW.convScalarOfLit_of PI.GGConvScalarW.representation_conjugate_gamma PI.GGConvScalarW.representation_commutes_gamma
    PI.GGConvScalarW.averaging_operator_idempotent PI.GGConvScalarW.generic_iff_criterion PI.GGConvScalarW.intertwiner_rank_le_one
    PI.GGConvScalarW.schur_lemma_complex PI.GGConvScalarW.trace_representation_gamma PI.GGConvScalarW.idempotent_trace_formula
    PI.GGConvScalarW.representation_dimension_pos
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
section
theorem n_unimodular_local : PI.NUnimodLoc.NUnimodLoc :=
  PI.NUnimodLoc.UnitaryGroupMassFormula.nUnimodLoc_of PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conjugation_unimodular
    PI.NUnimodLoc.UnitaryGroupMassFormula.TR.transfer_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormHSBlocks
section
theorem hilbert_schmidt_blocks : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevBasics
section
theorem level_basics : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
section
private theorem eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.EabH H a b (fun x => f (h * x)) = fun x => Formalism.QuantumDeterminants.EabH H a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV, mul_assoc]

private theorem qdTop_eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b (fun x => f (h * x)) =
      fun x => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, eabH_comp_mul_left]

private theorem foldr_apply_comp_mul_left_of_forall_mem {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ) (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (by simp [hT']))]
    exact hL T (by simp) _

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by
  intro E _ _ n t H f a b u h
  funext x
  simp only [Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hL : ∀ T ∈ List.ofFn (fun k : Fin t =>
      Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)),
      ∀ f' : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f' (h * x)) = fun x => T f' (h * x) := by
    intro T hT f'
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    exact qdTop_eabH_comp_mul_left H h _ _ _ f'
  rw [foldr_apply_comp_mul_left_of_forall_mem h _ hL f]

theorem quantum_minor_left : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiBuild
section
theorem sc_pi_construction : PI.ScPiExists.Build :=
  PI.ScPiBuildW.Asm.build
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
section
theorem weylForK_of : PI.WeylForU → PI.WeylForK :=
  PI.WeylForKWork.weylForK_of_leaves PI.WeylForKWork.block_reindex_holds PI.WeylForKWork.block_diagonal_torus_holds
    PI.WeylForKWork.torus_weight_exists PI.WeylForKWork.weight_unique_holds PI.WeylForKWork.minimal_irreducible_exists
    PI.WeylForKWork.dominant_restriction_holds PI.WeylForKWork.dimension_induction_holds PI.WeylForKWork.weyl_formula_compact
end

