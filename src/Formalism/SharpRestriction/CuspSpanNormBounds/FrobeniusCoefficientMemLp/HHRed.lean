module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoveringRadius.CoverRad
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h : (NumberField.discr D.host.E) ≠ 0 := NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h1
  simpa [Int.cast_abs] using h2

end Formalism.MainNotions.S.Pv.HH

end
