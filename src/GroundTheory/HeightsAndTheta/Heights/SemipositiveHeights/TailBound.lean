module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

end GroundTheory.Heights₂.Heights.ForSecondHalf
