module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0118
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
