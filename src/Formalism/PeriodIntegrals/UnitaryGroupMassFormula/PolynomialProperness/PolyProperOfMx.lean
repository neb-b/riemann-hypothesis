module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.SecondOrderNormBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029

@[expose] public section

namespace PI.PolynomialProperness

theorem polyProper_of_mx (hMX : MXFacts) : Formalism.FourierDecayAlt.C2.PolyProper := by
  have hT := tauMem_of hMX TauN.neFacts
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame
  exact polyProper_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of hU gvGroup) (frameSg_of hU hT gvGroup) (frameSg'_of hU hT gvGroup) (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
