module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiDerivative.StarinvDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiBigCellForm.BigCellEqW0BMulTM
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TaylorInversePower.SumMultinomialSub
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TiltedDivisibility.TiltDivOfGeneral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentValuation.VwIntEqZero
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowWtSpan
section
theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig
section
theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG
section
theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv
section
theorem phiDeriv_of (hW : PI.SwBig.LongWeylElementSquare) : PI.SwBig.PhiDeriv :=
  fun k r => PI.SwBig.PhiDerivW.main k r hW
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm
section
theorem phi_form' : PI.SwBig.PhiForm := PI.SwBig.PhiFormProof.phiForm
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TayInvPow
section
theorem coeffInversePowerFacts.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TiltDivisibility
section
theorem tilt_divisibility : PI.ArtSch.TiltDiv := PI.ArtSch.tiltDiv_of_general
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnipVal
section
theorem unipVal : PI.UnipVal.UnipVal := fun _ _ _ w =>
  ⟨fun n hn => PI.UnitaryGroupMassFormula.UnipVal.Main.part1 w n hn,
    fun g₁ g₂ a h1 h2 h12 => PI.UnitaryGroupMassFormula.UnipVal.Main.part2 w g₁ g₂ a h1 h2 h12⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VacEntire
section
theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
section
theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective
section
theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
end

