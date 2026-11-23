module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTest

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem dim_eq_of_nonempty {S : Scheme.{0}} (s : S) (P : PolAV S) {n : ℕ}
    (h : SmoothOfRelativeDimension n P.A.hom) : P.g = n :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h (eSec P.A s)

end GlobalTheory.PolTest
