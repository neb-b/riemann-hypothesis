module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AmplitudeOrbitalIntegral
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PeriodG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomTie
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0018
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeGapDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.HasDerivAtMatrixExpZero
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0001
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.AutomorphicTheory.RankOneTori.KDense

@[expose] public section

namespace CompanionTheory.Lime.BM

theorem wuDecayOfGap (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap h

theorem ampUnif (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.L2.S.Pv.AmpOrbCoef.BM.ampUnif_gap h
    fun k r ε lam H _ _ _ σ hl hσ v hv Ws hWs e he => Formalism.MainStatements.RankOne.KD.kDense k r ε lam H σ hl hσ v hv Ws hWs e he

end CompanionTheory.Lime.BM
