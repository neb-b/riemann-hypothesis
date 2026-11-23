module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.PB.Known

open ReciprocityTheory.ChartRestriction.G

theorem metricChange : AI.I2.MetricChangeStatement := Geo.metricChange

theorem divSuppArith : Geo.DivSuppArithStatement := Geo.divSuppArith

theorem genFibreExists : AI.I4.GenFibreExistsStatement := GroundTheory.Heights₂.Heights.Targets.genFibreExists

theorem fieldNumbers (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    AI.I1.ExistsUniqueStatement F ι ∧ AI.I1.SymmStatement F ι ∧ AI.I1.MultilinStatement F ι :=
  ⟨GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι, AI.I1.symm_thm F ι, AI.I1.multilin_thm F ι⟩

end GlobalTheory.CompanionTheory.Ar.PB.Known
