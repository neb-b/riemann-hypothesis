module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PTorsionEquidistribution
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Bundle0001

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem TorsionEquidistribution.full : TorsionEquidistribution.Statement :=
  TorsionEquidistribution.proof

theorem SupOfOrthonormalSum.full : SupOfOrthonormalSum.Statement.{u, v} :=
  SupOfOrthonormalSum.proof

theorem SlopeParameterChoice.full : SlopeParameterChoice.Statement :=
  SlopeParameterChoice.proof

end GroundTheory.Heights₂.Heights
