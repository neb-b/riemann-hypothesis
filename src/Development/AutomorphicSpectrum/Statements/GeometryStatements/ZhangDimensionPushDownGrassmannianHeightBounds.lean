module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace Prov

def HS : Prop :=
  SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticIntersectionNonneg ∧ ArithmeticVolumeLowerBound ∧ BirationalPullbackPushforwardFormula ∧ ArithmeticHilbertSamuelUpperBound ∧ ArithmeticHilbertSamuelUpperBoundNumberField ∧
    HilbertSamuel.G3.Statement ∧ HilbertSamuel.ArithmeticVolumeMultiplicative.Statement

def An : Prop :=
  ReciprocityTheory.AnForm.P.TailBoundStatement ∧ ReciprocityTheory.AnForm.P.ConvergenceStatement ∧
    ReciprocityTheory.AnForm.P.ConvergenceSignedStatement ∧ ReciprocityTheory.AnForm.P.ConvergenceRateStatement ∧
    ReciprocityTheory.AnForm.P.UnifIntStatement ∧ ReciprocityTheory.AnForm.P.PullbackStatement ∧ ReciprocityTheory.AnForm.P.RegGlobalStatement

def ZhangDimensionPushDownGrassmannianHeightBounds : Prop :=
  ZhangLowerX.Statement ∧ DimX.Statement ∧ True ∧ PushDown.Statement ∧ GrassmannianHeightZTwo.Statement

abbrev LemmaS := @SlopeBoundSt

end Prov

end GlobalTheory.CompanionTheory.Ar
