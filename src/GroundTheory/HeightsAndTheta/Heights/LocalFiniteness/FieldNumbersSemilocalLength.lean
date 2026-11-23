module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
