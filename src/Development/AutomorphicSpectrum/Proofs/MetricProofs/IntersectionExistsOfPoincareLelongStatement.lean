module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelong
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_exists_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | exact GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.thmIExists <;> assumption)
