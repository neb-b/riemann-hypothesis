module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Bundle0002

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

end GroundTheory.Heights₂.Heights.LowerBound
