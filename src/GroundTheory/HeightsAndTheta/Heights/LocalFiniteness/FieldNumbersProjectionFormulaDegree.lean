module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRFlagBundleLineBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ProjectionFormulaDegree.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.CutRational.full GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBase.full GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward
