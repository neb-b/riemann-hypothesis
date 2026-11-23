module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual
public import GroundTheory.FunctionField.DivisorDegree
public import GroundTheory.FunctionField.WeilDifferential

@[expose] public section

open CategoryTheory AlgebraicGeometry Order Topology Module MonoidalCategory

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField]


omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in
noncomputable def invertibleDegree {L : X.Modules} (hL : IsInvertibleSheaf L) : ℤ :=
  WeilDivisor.degree (k := k) (divisorOfInvertible hL)



variable (hX : topologicalKrullDim X ≤ 1)

noncomputable def canonicalDifferential : WeilDifferential k X.functionField :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose


noncomputable def canonicalDivisor : WeilDivisor X :=
  (divisorEquiv (k := k) hX).symm (canonicalDifferential (k := k) (X := X)).divisor

noncomputable def canonicalSheaf : X.Modules :=
  divisorSheaf (canonicalDivisor (k := k) hX)

end GroundTheory.Arith.SchemeCoh
