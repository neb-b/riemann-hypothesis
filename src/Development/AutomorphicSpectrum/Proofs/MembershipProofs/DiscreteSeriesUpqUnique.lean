module

public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.InertJacobiLevels.SecondTorsionCardPos
public import Formalism.SharpRestriction.InertJacobiLevels.AsmRec
public import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.DefsInst
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115

@[expose] public section

namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique :=
  fun n ε lam hlam H H' _ _ _ _ σ σ' hσ hσ' =>
    GlobalTheory.CompanionTheory.DSUniq.ds_unique
      _root_.CompanionTheory.D.LK.hMultAlg _root_.CompanionTheory.D.LK.hKModExists
      _root_.CompanionTheory.D.LK.hOrthCyc n ε lam H H' σ σ' hlam hσ hσ'

end GlobalTheory.CompanionTheory.Front
