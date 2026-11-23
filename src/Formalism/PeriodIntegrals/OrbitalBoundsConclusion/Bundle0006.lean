module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Weight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmithNormalForm.ExistsMoveRow
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.ExistsUnitDiff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianUniqueness.GaussUniqMain
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain
public import Formalism.PeriodIntegrals.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
section
theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
section
namespace PI

theorem wqUnique : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter
section
theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SmithMat
section
theorem smith_normal_form_theory.{u} : PI.SmithMat.{u} := by
  intro R _ _ _ n A
  obtain ⟨d, ⟨U, V, hU, hV, h⟩, hd⟩ := PI.SmithWork.smith n A
  exact ⟨U, V, d, hU, hV, h, hd⟩

theorem smith_diagonal_entries.{u} : PI.SmithDiag.{u} := by
  intro R _ _ _ n A
  obtain ⟨U, V, d, hU, hV, h, -⟩ := smith_normal_form_theory R n A
  exact ⟨U, V, d, hU, hV, h⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
section
theorem split_integral_local : PI.SplitIntLoc := PI.SplitIntLoc.Proof.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq
section
theorem gauss_sum_unique : PI.SwBig.GaussUniq := PI.SwBig.GU.gaussUniq_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SymDist
section
theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TensCpctDen
section
theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne
section
theorem TwChrOne : PI.TwChrOne.TwChrOne := PI.TwChrOne.Pf.twChrOne_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeakApproxDVR
section
theorem weak_approximation_dvr : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittUnram
section
theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
section
theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
end

