module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.FlagImmersions.RealTowerMeanSlopeCondition

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem tower_A1_of_real_tower : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T),
      R.Smooth → R.Flat → R.Pos → T.A1 :=
  @RootFieldNumerics.real_tower_mean_slope_condition

end GlobalTheory.CompanionTheory.Ar.Top
