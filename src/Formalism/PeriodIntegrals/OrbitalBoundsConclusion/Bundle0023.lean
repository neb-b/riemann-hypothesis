module

public import Mathlib
public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.LeftMultiplicationRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PrincipalIdealRingAtPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence
public import Formalism.PeriodIntegrals.UJClassFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
section
theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv
section
namespace PI

theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OmFibreUniq
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem omUnique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : ℕ) :
    PI.OmFibreUniq.OmUnique σ J ψ v a :=
  PI.OmFibreUniq.W.omUnique_of_sdEx
    (PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT PI.OmFibreUniq.W.Sd.additive_character_nontrivial) σ J ψ v a
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
section
theorem qmCapComm_of : Formalism.FourierDecayAlt.Q.EabPres → Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  fun hP hG => QmCapCommW.capelli_operator_transfer QmCapCommW.capelli_operator_congruence QmCapCommW.quantum_determinant_commutes hP hG

theorem qmCapComm_of_gl : Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of qnEabPres

theorem capelli_det_commute : Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of_gl qnEabGl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
section
theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft
section
theorem qnRuleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScRefExists
section
theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
section
theorem unitary_class_set_finite : PI.UJClassFin.UJClassFin :=
  PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds
    PI.UnitaryGroupMassFormula.UJClassFin.adelic_bounds PI.UnitaryGroupMassFormula.UJClassFin.lattice_classes_finite_refinement
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost
section
theorem operator_word_cost : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  PI.UnitaryGroupMassFormula.UsCost.unitarySum_cost_of_parts PI.UnitaryGroupMassFormula.UsCost.wordsId PI.UnitaryGroupMassFormula.UsCost.letterSize PI.UnitaryGroupMassFormula.UsCost.starScale
    PI.UnitaryGroupMassFormula.UsCost.commLR PI.UnitaryGroupMassFormula.UsCost.offK PI.UnitaryGroupMassFormula.UsCost.zSmooth
    (PI.UnitaryGroupMassFormula.UsCost.zCost_of PI.UnitaryGroupMassFormula.UsCost.zSmooth PI.UnitaryGroupMassFormula.UsCost.zDeriv PI.UnitaryGroupMassFormula.UsCost.dirSize)
end

