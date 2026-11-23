module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0155
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (_root_.GlobalTheory.MomFin.moments_fin GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItemsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_signature_indep_and_classNumberItems : (∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) → ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  first | exact @GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | exact GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | (intros; apply GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume <;> assumption)
end

