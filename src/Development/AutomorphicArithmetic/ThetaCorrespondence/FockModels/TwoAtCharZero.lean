module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MultiAt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.Bundle0001

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL NumberField IsDedekindDomain

namespace UpperTheory.Lit.Mix

theorem twoAt_charZero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] :
    TwoAt k :=
  PositivityTheory.RgUd.bern k

end UpperTheory.Lit.Mix
