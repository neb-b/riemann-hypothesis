module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement :=
  GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
