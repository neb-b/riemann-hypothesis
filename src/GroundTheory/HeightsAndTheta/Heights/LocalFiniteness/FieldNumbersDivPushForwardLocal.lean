module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength
