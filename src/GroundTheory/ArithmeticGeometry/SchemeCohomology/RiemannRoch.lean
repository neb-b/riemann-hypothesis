module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
public import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCanonical
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
public import GroundTheory.FunctionField.WeilDifferential

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module MonoidalCategory

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [IsNormalScheme X]

section Instances

variable (hX : topologicalKrullDim X = 1)


omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
include hX in
theorem curve_instances :
    IsNoetherian X ∧ IsLocallyFactorial X ∧ IsFunctionField k X.functionField := by
  have : IsNoetherian X := isNoetherian_of_finiteType (k := k) X
  exact ⟨this, isLocallyFactorial_of_dim_le_one hX.le, isFunctionField X hX⟩

end Instances

section Genus



end Genus

section Degree

noncomputable def sheafDegree (hX : topologicalKrullDim X = 1) {L : X.Modules}
    (hL : IsInvertibleSheaf L) : ℤ :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  invertibleDegree (k := k) hL

end Degree

section Canonical

noncomputable def omega (hX : topologicalKrullDim X = 1) : X.Modules :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  canonicalSheaf (k := k) hX.le

end Canonical

section RiemannRoch

end RiemannRoch

end GroundTheory.Arith.SchemeCoh
