module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0003
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ExistsNormEqTwoPow
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HermFrameHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

@[expose] public section

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.H (localStandard kappaExists)

theorem frameExistsH : FrameExistsH := FrP.hermFrame_holds

theorem uniformGaussModels_fact_variant : ThetaFourthPowerShapeNormalised := theta_kappa_shape_holds localStandard kappaExists

theorem frobExistsH : FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

end Formalism.L2.Th1.Top
